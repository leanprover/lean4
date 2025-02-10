// Lean compiler output
// Module: Lean.Elab.Tactic.Grind
// Imports: Init.Grind.Tactics Lean.Meta.Tactic.Grind Lean.Meta.Tactic.TryThis Lean.Elab.Command Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Config
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___boxed(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__4;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__17;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_grind___closed__2;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__2;
lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrind___closed__2;
lean_object* lean_private_to_user_name(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrindTrace___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__31;
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addEMatchTheorem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_mkGrindOnly___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkGrindOnly___closed__3;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__4;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16;
static lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__4(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_grind___closed__1;
uint8_t l_Lean_Meta_Match_isMatchEqnTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__9;
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grindParamsPos;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_isGrindOnly___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__3(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__17;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrindCore___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalGrindCore___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2;
uint8_t l_Lean_LocalContext_usesUserName(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__1;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__1;
static lean_object* l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_List_filterMapTR_go___at_Lean_preprocessSyntaxAndResolve___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
static lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__1;
lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__1;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_filterFieldList___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grindOnlyPos;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessPattern(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__2;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5;
lean_object* l_Lean_Meta_Grind_EMatchTheorems_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__22;
static lean_object* l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grind_warning;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__11;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_resetCasesExt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__3;
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__2;
lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__5;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__29;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
static lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__3;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__24;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPArray_x27___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Result_hasFailures(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__5;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkGrindParams___closed__1;
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__10;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalGrind___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__6;
extern lean_object* l_Lean_rootNamespace;
lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_mkGrindOnly___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__3;
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_elabGrindPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__12;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__14;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15;
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveLocalName_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__7;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__11;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__34;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__3;
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__5;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__4;
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__8;
lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4;
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__4;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__4;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___closed__1;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__1(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getCasesTypes___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__4;
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__6;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__3;
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__8;
lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__13___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__2;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4;
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
lean_object* l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__6;
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_setGrindParams___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__26;
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
static lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___closed__1;
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10;
static lean_object* l_Lean_Elab_Tactic_mkGrindOnly___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isGrindOnly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__1___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__8;
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isGrindOnly___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrindCore___closed__4;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__5;
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__3;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___at_Lean_filterFieldList___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrindTrace___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalGrindCore___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_object* l_Lean_Meta_Grind_getEMatchTheorems___rarg(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Config", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2;
x_3 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4;
x_10 = 0;
x_11 = l_Lean_Meta_evalExpr_x27___rarg(x_9, x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration\n", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nException: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_22 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Exception_toMessageData(x_16);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_41 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Exception_toMessageData(x_35);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
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
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configuration contains 'sorry'", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasSorry(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__2;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = 1;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_alloc_ctor(0, 6, 8);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set(x_7, 5, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 2, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 4, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 5, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 6, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 7, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4;
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
x_18 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__2(x_14, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
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
x_19 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1;
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
x_24 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__2(x_20, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
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
x_25 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1;
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
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("error evaluating configuration, environment does not yet contain type ", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4;
x_2 = l_Lean_MessageData_ofName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__2;
x_2 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__4;
x_2 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_15 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4;
x_16 = l_Lean_Environment_contains(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_2);
x_17 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__5;
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
x_24 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__3(x_1, x_2, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4(x_11, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_37 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4(x_11, x_13, x_36, x_4, x_5, x_6, x_7, x_35, x_9, x_10);
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
x_38 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__4(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_elabGrindConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_1, x_9);
x_11 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_List_mapTR_loop___at_Lean_filterFieldList___spec__2(x_1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_box(0);
x_11 = l_List_filterTR_loop___at_Lean_filterFieldList___spec__1(x_2, x_10);
x_12 = l_List_isEmpty___rarg(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___lambda__1(x_11, x_10, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
x_15 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveLocalName_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_26 = lean_ctor_get(x_7, 11);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_28 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_18);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*12, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*12 + 1, x_27);
x_30 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_9);
lean_dec(x_29);
return x_30;
}
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected identifier", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
x_13 = l_List_filterMapTR_go___at_Lean_preprocessSyntaxAndResolve___spec__1(x_11, x_12);
x_14 = l_List_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 5);
x_18 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_18);
x_19 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
x_26 = lean_ctor_get(x_7, 6);
x_27 = lean_ctor_get(x_7, 7);
x_28 = lean_ctor_get(x_7, 8);
x_29 = lean_ctor_get(x_7, 9);
x_30 = lean_ctor_get(x_7, 10);
x_31 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_32 = lean_ctor_get(x_7, 11);
x_33 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
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
lean_dec(x_7);
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
x_36 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_35, x_8, x_9);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
x_37 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3;
x_38 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2___closed__1;
x_10 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_Lean_instInhabitedName;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_26 = lean_ctor_get(x_7, 11);
x_27 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_28 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_18);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*12, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*12 + 1, x_27);
x_30 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_9);
lean_dec(x_29);
return x_30;
}
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__1;
x_2 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__2;
x_3 = lean_unsigned_to_nat(364u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous identifier '", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', possible interpretations: ", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__4;
x_11 = l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_20 = l_Lean_Syntax_formatStxAux(x_17, x_18, x_19, x_1);
x_21 = l_Std_Format_defWidth;
x_22 = lean_format_pretty(x_20, x_21, x_19, x_19);
x_23 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__5;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__6;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(x_2, x_27);
x_29 = l_List_toString___at_Lean_ensureNoOverload___spec__2(x_28);
lean_dec(x_28);
x_30 = lean_string_append(x_26, x_29);
lean_dec(x_29);
x_31 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__10(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_elabGrindPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___boxed), 8, 0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_5, x_4, x_16);
x_18 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l_Lean_Elab_Term_elabTerm(x_15, x_1, x_18, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(x_6, x_7, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Meta_Grind_preprocessPattern(x_25, x_18, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_expr_abstract(x_28, x_2);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_33 = lean_array_uset(x_17, x_4, x_30);
x_4 = x_32;
x_5 = x_33;
x_12 = x_29;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = lean_box(0);
x_13 = 0;
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(x_13, x_12, x_1, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = l_Lean_Syntax_TSepArray_getElems___rarg(x_1);
x_14 = lean_array_size(x_13);
x_15 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(x_2, x_4, x_14, x_15, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_4);
x_20 = lean_array_to_list(x_17);
x_21 = 9;
x_22 = l_Lean_Meta_Grind_addEMatchTheorem(x_3, x_19, x_20, x_21, x_8, x_9, x_10, x_11, x_18);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_elabGrindPattern___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_11);
x_13 = l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_addTermInfo(x_1, x_14, x_16, x_16, x_17, x_18, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_3);
lean_inc(x_11);
x_21 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_ConstantInfo_type(x_22);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabGrindPattern___lambda__1___boxed), 12, 3);
lean_closure_set(x_25, 0, x_2);
lean_closure_set(x_25, 1, x_16);
lean_closure_set(x_25, 2, x_11);
x_26 = l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg(x_24, x_25, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindPattern", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Lean_Elab_Tactic_elabGrindPattern___closed__2;
x_4 = l_Lean_Elab_Tactic_elabGrindPattern___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_elabGrindPattern___closed__4;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_Tactic_elabGrindPattern___closed__6;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabGrindPattern___lambda__2), 9, 2);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Command_liftTermElabM___rarg(x_16, x_2, x_3, x_4);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_elabGrindPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_elabGrindPattern(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabGrindPattern", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabGrindPattern___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5;
x_3 = l_Lean_Elab_Tactic_elabGrindPattern___closed__4;
x_4 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_Grind_resetCasesExt___rarg(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Meta_Grind_resetEMatchTheoremsExt___rarg(x_6, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___closed__1;
x_5 = l_Lean_Elab_Command_liftTermElabM___rarg(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabResetGrindAttrs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_elabResetGrindAttrs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("resetGrindAttrs", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabResetGrindAttrs", 19, 19);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabResetGrindAttrs___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_13, x_16, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_15, x_2, x_18);
x_2 = x_21;
x_3 = x_22;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_size(x_4);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1(x_15, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_registerNormTheorems(x_13, x_17, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_17);
lean_dec(x_13);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
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
lean_dec(x_4);
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
static lean_object* _init_l_Lean_Elab_Tactic_elabInitGrindNorm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initGrindNorm", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Lean_Elab_Tactic_elabGrindPattern___closed__2;
x_4 = l_Lean_Elab_Tactic_elabInitGrindNorm___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabInitGrindNorm___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Widget_elabShowPanelWidgetsCmd___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_14 = lean_array_size(x_13);
x_15 = lean_box_usize(x_14);
x_16 = l_Lean_Elab_Tactic_elabInitGrindNorm___boxed__const__1;
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1___boxed), 11, 4);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_13);
lean_closure_set(x_17, 3, x_12);
x_18 = l_Lean_Elab_Command_liftTermElabM___rarg(x_17, x_2, x_3, x_4);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_elabInitGrindNorm(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabInitGrindNorm", 17, 17);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabInitGrindNorm___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5;
x_3 = l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to genereate equation theorems for `", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_MessageData_ofName(x_1);
x_13 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1(x_16, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_9, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 3);
x_23 = l_Array_toPArray_x27___rarg(x_20);
lean_dec(x_20);
x_24 = l_Lean_PersistentArray_append___rarg(x_22, x_23);
lean_dec(x_23);
lean_ctor_set(x_2, 3, x_24);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_ctor_get(x_2, 4);
x_30 = lean_ctor_get(x_2, 5);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_31 = l_Array_toPArray_x27___rarg(x_20);
lean_dec(x_20);
x_32 = l_Lean_PersistentArray_append___rarg(x_28, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_30);
lean_ctor_set(x_9, 0, x_33);
return x_9;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_dec(x_9);
x_35 = lean_ctor_get(x_10, 0);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_41);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_42 = x_2;
} else {
 lean_dec_ref(x_2);
 x_42 = lean_box(0);
}
x_43 = l_Array_toPArray_x27___rarg(x_35);
lean_dec(x_35);
x_44 = l_Lean_PersistentArray_append___rarg(x_39, x_43);
lean_dec(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 6, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_40);
lean_ctor_set(x_45, 5, x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid `grind` parameter, `", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is a definition, the only acceptable (and redundant) modifier is '='", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; 
x_10 = 0;
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(x_3, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = 8;
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
x_14 = l_Lean_MessageData_ofName(x_1);
x_15 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_18, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1(x_1, x_2, x_24, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1(x_1, x_2, x_26, x_5, x_6, x_7, x_8, x_9);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is a reducible definition, `grind` automatically unfolds them", 63, 63);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is not a theorem, definition, or inductive type", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 2;
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_1, 3);
x_19 = l_Lean_PersistentArray_push___rarg(x_18, x_17);
lean_ctor_set(x_1, 3, x_19);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_1, 4);
x_26 = lean_ctor_get(x_1, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_27 = l_Lean_PersistentArray_push___rarg(x_24, x_20);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 5);
lean_inc(x_36);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_37 = x_1;
} else {
 lean_dec_ref(x_1);
 x_37 = lean_box(0);
}
x_38 = l_Lean_PersistentArray_push___rarg(x_34, x_29);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 6, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_35);
lean_ctor_set(x_39, 5, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; lean_object* x_46; 
x_45 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_46 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_45, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
x_52 = lean_ctor_get(x_1, 2);
x_53 = lean_ctor_get(x_1, 3);
x_54 = lean_ctor_get(x_1, 4);
x_55 = lean_ctor_get(x_1, 5);
x_56 = l_Lean_PersistentArray_push___rarg(x_53, x_47);
x_57 = 1;
x_58 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_57, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = l_Lean_PersistentArray_push___rarg(x_56, x_60);
lean_ctor_set(x_1, 3, x_61);
lean_ctor_set(x_58, 0, x_1);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = l_Lean_PersistentArray_push___rarg(x_56, x_62);
lean_ctor_set(x_1, 3, x_64);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_56);
lean_free_object(x_1);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
x_66 = !lean_is_exclusive(x_58);
if (x_66 == 0)
{
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_1, 0);
x_71 = lean_ctor_get(x_1, 1);
x_72 = lean_ctor_get(x_1, 2);
x_73 = lean_ctor_get(x_1, 3);
x_74 = lean_ctor_get(x_1, 4);
x_75 = lean_ctor_get(x_1, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_1);
x_76 = l_Lean_PersistentArray_push___rarg(x_73, x_47);
x_77 = 1;
x_78 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_77, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = l_Lean_PersistentArray_push___rarg(x_76, x_79);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_70);
lean_ctor_set(x_83, 1, x_71);
lean_ctor_set(x_83, 2, x_72);
lean_ctor_set(x_83, 3, x_82);
lean_ctor_set(x_83, 4, x_74);
lean_ctor_set(x_83, 5, x_75);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_46);
if (x_89 == 0)
{
return x_46;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_46, 0);
x_91 = lean_ctor_get(x_46, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_46);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
case 1:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_10);
x_93 = lean_ctor_get(x_9, 1);
lean_inc(x_93);
lean_dec(x_9);
lean_inc(x_2);
x_94 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_2, x_4, x_5, x_6, x_7, x_93);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_box(0);
x_99 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2(x_2, x_1, x_3, x_98, x_4, x_5, x_6, x_7, x_97);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_94);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_101 = lean_ctor_get(x_94, 1);
x_102 = lean_ctor_get(x_94, 0);
lean_dec(x_102);
x_103 = l_Lean_MessageData_ofName(x_2);
x_104 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4;
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_103);
lean_ctor_set(x_94, 0, x_104);
x_105 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_106, x_4, x_5, x_6, x_7, x_101);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
return x_107;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_107);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_112 = lean_ctor_get(x_94, 1);
lean_inc(x_112);
lean_dec(x_94);
x_113 = l_Lean_MessageData_ofName(x_2);
x_114 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_117, x_4, x_5, x_6, x_7, x_112);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
case 2:
{
lean_object* x_123; uint8_t x_124; uint8_t x_125; 
lean_dec(x_10);
x_123 = lean_ctor_get(x_9, 1);
lean_inc(x_123);
lean_dec(x_9);
x_124 = 2;
x_125 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(x_3, x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_3, x_4, x_5, x_6, x_7, x_123);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_1);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_126, 0);
x_130 = lean_ctor_get(x_1, 3);
x_131 = l_Lean_PersistentArray_push___rarg(x_130, x_129);
lean_ctor_set(x_1, 3, x_131);
lean_ctor_set(x_126, 0, x_1);
return x_126;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_132 = lean_ctor_get(x_126, 0);
x_133 = lean_ctor_get(x_1, 0);
x_134 = lean_ctor_get(x_1, 1);
x_135 = lean_ctor_get(x_1, 2);
x_136 = lean_ctor_get(x_1, 3);
x_137 = lean_ctor_get(x_1, 4);
x_138 = lean_ctor_get(x_1, 5);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_1);
x_139 = l_Lean_PersistentArray_push___rarg(x_136, x_132);
x_140 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_140, 2, x_135);
lean_ctor_set(x_140, 3, x_139);
lean_ctor_set(x_140, 4, x_137);
lean_ctor_set(x_140, 5, x_138);
lean_ctor_set(x_126, 0, x_140);
return x_126;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_141 = lean_ctor_get(x_126, 0);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_126);
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_1, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_1, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_1, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_1, 5);
lean_inc(x_148);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_149 = x_1;
} else {
 lean_dec_ref(x_1);
 x_149 = lean_box(0);
}
x_150 = l_Lean_PersistentArray_push___rarg(x_146, x_141);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 6, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_143);
lean_ctor_set(x_151, 1, x_144);
lean_ctor_set(x_151, 2, x_145);
lean_ctor_set(x_151, 3, x_150);
lean_ctor_set(x_151, 4, x_147);
lean_ctor_set(x_151, 5, x_148);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_142);
return x_152;
}
}
else
{
uint8_t x_153; 
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_126);
if (x_153 == 0)
{
return x_126;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_126, 0);
x_155 = lean_ctor_get(x_126, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_126);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; lean_object* x_158; 
x_157 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_158 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_157, x_4, x_5, x_6, x_7, x_123);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = !lean_is_exclusive(x_1);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_162 = lean_ctor_get(x_1, 0);
x_163 = lean_ctor_get(x_1, 1);
x_164 = lean_ctor_get(x_1, 2);
x_165 = lean_ctor_get(x_1, 3);
x_166 = lean_ctor_get(x_1, 4);
x_167 = lean_ctor_get(x_1, 5);
x_168 = l_Lean_PersistentArray_push___rarg(x_165, x_159);
x_169 = 1;
x_170 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_169, x_4, x_5, x_6, x_7, x_160);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = l_Lean_PersistentArray_push___rarg(x_168, x_172);
lean_ctor_set(x_1, 3, x_173);
lean_ctor_set(x_170, 0, x_1);
return x_170;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_170, 0);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_170);
x_176 = l_Lean_PersistentArray_push___rarg(x_168, x_174);
lean_ctor_set(x_1, 3, x_176);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_1);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
uint8_t x_178; 
lean_dec(x_168);
lean_free_object(x_1);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
x_178 = !lean_is_exclusive(x_170);
if (x_178 == 0)
{
return x_170;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_170, 0);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_170);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
x_182 = lean_ctor_get(x_1, 0);
x_183 = lean_ctor_get(x_1, 1);
x_184 = lean_ctor_get(x_1, 2);
x_185 = lean_ctor_get(x_1, 3);
x_186 = lean_ctor_get(x_1, 4);
x_187 = lean_ctor_get(x_1, 5);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_1);
x_188 = l_Lean_PersistentArray_push___rarg(x_185, x_159);
x_189 = 1;
x_190 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_189, x_4, x_5, x_6, x_7, x_160);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
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
x_194 = l_Lean_PersistentArray_push___rarg(x_188, x_191);
x_195 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_195, 0, x_182);
lean_ctor_set(x_195, 1, x_183);
lean_ctor_set(x_195, 2, x_184);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 4, x_186);
lean_ctor_set(x_195, 5, x_187);
if (lean_is_scalar(x_193)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_193;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_192);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
x_197 = lean_ctor_get(x_190, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_190, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_199 = x_190;
} else {
 lean_dec_ref(x_190);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_158);
if (x_201 == 0)
{
return x_158;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_158, 0);
x_203 = lean_ctor_get(x_158, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_158);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
case 6:
{
lean_object* x_205; uint8_t x_206; uint8_t x_207; 
lean_dec(x_10);
x_205 = lean_ctor_get(x_9, 1);
lean_inc(x_205);
lean_dec(x_9);
x_206 = 2;
x_207 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(x_3, x_206);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_3, x_4, x_5, x_6, x_7, x_205);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_1);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_208, 0);
x_212 = lean_ctor_get(x_1, 3);
x_213 = l_Lean_PersistentArray_push___rarg(x_212, x_211);
lean_ctor_set(x_1, 3, x_213);
lean_ctor_set(x_208, 0, x_1);
return x_208;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_214 = lean_ctor_get(x_208, 0);
x_215 = lean_ctor_get(x_1, 0);
x_216 = lean_ctor_get(x_1, 1);
x_217 = lean_ctor_get(x_1, 2);
x_218 = lean_ctor_get(x_1, 3);
x_219 = lean_ctor_get(x_1, 4);
x_220 = lean_ctor_get(x_1, 5);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_1);
x_221 = l_Lean_PersistentArray_push___rarg(x_218, x_214);
x_222 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_222, 0, x_215);
lean_ctor_set(x_222, 1, x_216);
lean_ctor_set(x_222, 2, x_217);
lean_ctor_set(x_222, 3, x_221);
lean_ctor_set(x_222, 4, x_219);
lean_ctor_set(x_222, 5, x_220);
lean_ctor_set(x_208, 0, x_222);
return x_208;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_223 = lean_ctor_get(x_208, 0);
x_224 = lean_ctor_get(x_208, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_208);
x_225 = lean_ctor_get(x_1, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_1, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_1, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 3);
lean_inc(x_228);
x_229 = lean_ctor_get(x_1, 4);
lean_inc(x_229);
x_230 = lean_ctor_get(x_1, 5);
lean_inc(x_230);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_231 = x_1;
} else {
 lean_dec_ref(x_1);
 x_231 = lean_box(0);
}
x_232 = l_Lean_PersistentArray_push___rarg(x_228, x_223);
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(0, 6, 0);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_226);
lean_ctor_set(x_233, 2, x_227);
lean_ctor_set(x_233, 3, x_232);
lean_ctor_set(x_233, 4, x_229);
lean_ctor_set(x_233, 5, x_230);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_224);
return x_234;
}
}
else
{
uint8_t x_235; 
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_208);
if (x_235 == 0)
{
return x_208;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_208, 0);
x_237 = lean_ctor_get(x_208, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_208);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
uint8_t x_239; lean_object* x_240; 
x_239 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_240 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_239, x_4, x_5, x_6, x_7, x_205);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = !lean_is_exclusive(x_1);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
x_244 = lean_ctor_get(x_1, 0);
x_245 = lean_ctor_get(x_1, 1);
x_246 = lean_ctor_get(x_1, 2);
x_247 = lean_ctor_get(x_1, 3);
x_248 = lean_ctor_get(x_1, 4);
x_249 = lean_ctor_get(x_1, 5);
x_250 = l_Lean_PersistentArray_push___rarg(x_247, x_241);
x_251 = 1;
x_252 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_251, x_4, x_5, x_6, x_7, x_242);
if (lean_obj_tag(x_252) == 0)
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_252, 0);
x_255 = l_Lean_PersistentArray_push___rarg(x_250, x_254);
lean_ctor_set(x_1, 3, x_255);
lean_ctor_set(x_252, 0, x_1);
return x_252;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_252, 0);
x_257 = lean_ctor_get(x_252, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_252);
x_258 = l_Lean_PersistentArray_push___rarg(x_250, x_256);
lean_ctor_set(x_1, 3, x_258);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_1);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
uint8_t x_260; 
lean_dec(x_250);
lean_free_object(x_1);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_244);
x_260 = !lean_is_exclusive(x_252);
if (x_260 == 0)
{
return x_252;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_252, 0);
x_262 = lean_ctor_get(x_252, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_252);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; 
x_264 = lean_ctor_get(x_1, 0);
x_265 = lean_ctor_get(x_1, 1);
x_266 = lean_ctor_get(x_1, 2);
x_267 = lean_ctor_get(x_1, 3);
x_268 = lean_ctor_get(x_1, 4);
x_269 = lean_ctor_get(x_1, 5);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_1);
x_270 = l_Lean_PersistentArray_push___rarg(x_267, x_241);
x_271 = 1;
x_272 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_271, x_4, x_5, x_6, x_7, x_242);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
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
x_276 = l_Lean_PersistentArray_push___rarg(x_270, x_273);
x_277 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_277, 0, x_264);
lean_ctor_set(x_277, 1, x_265);
lean_ctor_set(x_277, 2, x_266);
lean_ctor_set(x_277, 3, x_276);
lean_ctor_set(x_277, 4, x_268);
lean_ctor_set(x_277, 5, x_269);
if (lean_is_scalar(x_275)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_275;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_274);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
x_279 = lean_ctor_get(x_272, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_272, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_281 = x_272;
} else {
 lean_dec_ref(x_272);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_283 = !lean_is_exclusive(x_240);
if (x_283 == 0)
{
return x_240;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_240, 0);
x_285 = lean_ctor_get(x_240, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_240);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
default: 
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_10);
lean_dec(x_1);
x_287 = lean_ctor_get(x_9, 1);
lean_inc(x_287);
lean_dec(x_9);
x_288 = l_Lean_MessageData_ofName(x_2);
x_289 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2;
x_290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_288);
x_291 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4;
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_293 = l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1(x_292, x_4, x_5, x_6, x_7, x_287);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_293;
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_294 = !lean_is_exclusive(x_9);
if (x_294 == 0)
{
return x_9;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_9, 0);
x_296 = lean_ctor_get(x_9, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_9);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*6);
x_8 = 9;
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(x_7, x_8);
if (x_9 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_ctor_get_uint8(x_12, sizeof(void*)*6);
x_15 = 9;
x_16 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1336_(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_12);
x_1 = x_13;
goto _start;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_13;
x_2 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 3);
x_17 = l_Lean_PersistentArray_push___rarg(x_16, x_13);
lean_ctor_set(x_5, 3, x_17);
x_4 = x_14;
x_6 = lean_box(0);
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_ctor_get(x_5, 3);
x_23 = lean_ctor_get(x_5, 4);
x_24 = lean_ctor_get(x_5, 5);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_25 = l_Lean_PersistentArray_push___rarg(x_22, x_13);
x_26 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set(x_26, 5, x_24);
x_4 = x_14;
x_5 = x_26;
x_6 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 3);
x_20 = lean_ctor_get(x_10, 4);
x_21 = lean_ctor_get(x_10, 5);
x_22 = lean_ctor_get(x_10, 6);
x_23 = lean_ctor_get(x_10, 7);
x_24 = lean_ctor_get(x_10, 8);
x_25 = lean_ctor_get(x_10, 9);
x_26 = lean_ctor_get(x_10, 10);
x_27 = lean_ctor_get_uint8(x_10, sizeof(void*)*12);
x_28 = lean_ctor_get(x_10, 11);
x_29 = lean_ctor_get_uint8(x_10, sizeof(void*)*12 + 1);
x_30 = l_Lean_replaceRef(x_1, x_21);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_31 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_20);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*12, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*12 + 1, x_29);
x_32 = 8;
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_6, x_14, x_32, x_8, x_9, x_31, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_5 = x_15;
x_6 = x_34;
x_7 = lean_box(0);
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 2);
x_19 = lean_ctor_get(x_10, 3);
x_20 = lean_ctor_get(x_10, 4);
x_21 = lean_ctor_get(x_10, 5);
x_22 = lean_ctor_get(x_10, 6);
x_23 = lean_ctor_get(x_10, 7);
x_24 = lean_ctor_get(x_10, 8);
x_25 = lean_ctor_get(x_10, 9);
x_26 = lean_ctor_get(x_10, 10);
x_27 = lean_ctor_get_uint8(x_10, sizeof(void*)*12);
x_28 = lean_ctor_get(x_10, 11);
x_29 = lean_ctor_get_uint8(x_10, sizeof(void*)*12 + 1);
x_30 = l_Lean_replaceRef(x_1, x_21);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_31 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_20);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*12, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*12 + 1, x_29);
x_32 = 8;
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_6, x_14, x_32, x_8, x_9, x_31, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_5 = x_15;
x_6 = x_34;
x_7 = lean_box(0);
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__2(x_1, x_9, x_1, x_1, x_2, lean_box(0), x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid use of `usr` modifier, `", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` does not have patterns specified with the command `grind_pattern`", 67, 67);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Meta_Grind_getEMatchTheorems___rarg(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lean_Meta_Grind_EMatchTheorems_find(x_12, x_14);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = l_List_filterTR_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(x_15, x_16);
x_18 = l_List_isEmpty___rarg(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_10);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__1(x_17, x_3, x_19, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_3);
x_21 = l_Lean_MessageData_ofName(x_1);
x_22 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__2;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_21);
lean_ctor_set(x_10, 0, x_22);
x_23 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwErrorAt___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__3(x_2, x_24, x_5, x_6, x_7, x_8, x_13);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
lean_inc(x_1);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_33 = l_Lean_Meta_Grind_EMatchTheorems_find(x_30, x_32);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l_List_filterTR_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(x_33, x_34);
x_36 = l_List_isEmpty___rarg(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_box(0);
x_38 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__1(x_35, x_3, x_37, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_7);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_35);
lean_dec(x_3);
x_39 = l_Lean_MessageData_ofName(x_1);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__2;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwErrorAt___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__3(x_2, x_43, x_5, x_6, x_7, x_8, x_31);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid use of `intro` modifier, `", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is not an inductive predicate", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_ctor_get_uint8(x_5, 0);
x_12 = lean_box(x_11);
if (lean_obj_tag(x_12) == 9)
{
if (x_3 == 0)
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_8, 5);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_ctor_set(x_8, 5, x_15);
x_16 = l_Lean_Meta_Grind_throwInvalidUsrModifier___rarg(x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 2);
x_24 = lean_ctor_get(x_8, 3);
x_25 = lean_ctor_get(x_8, 4);
x_26 = lean_ctor_get(x_8, 5);
x_27 = lean_ctor_get(x_8, 6);
x_28 = lean_ctor_get(x_8, 7);
x_29 = lean_ctor_get(x_8, 8);
x_30 = lean_ctor_get(x_8, 9);
x_31 = lean_ctor_get(x_8, 10);
x_32 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_33 = lean_ctor_get(x_8, 11);
x_34 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_33);
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
lean_dec(x_8);
x_35 = l_Lean_replaceRef(x_1, x_26);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
lean_ctor_set(x_36, 5, x_35);
lean_ctor_set(x_36, 6, x_27);
lean_ctor_set(x_36, 7, x_28);
lean_ctor_set(x_36, 8, x_29);
lean_ctor_set(x_36, 9, x_30);
lean_ctor_set(x_36, 10, x_31);
lean_ctor_set(x_36, 11, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*12, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*12 + 1, x_34);
x_37 = l_Lean_Meta_Grind_throwInvalidUsrModifier___rarg(x_36, x_9, x_10);
lean_dec(x_9);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2(x_2, x_1, x_4, x_42, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 5);
x_46 = l_Lean_replaceRef(x_1, x_45);
lean_dec(x_45);
lean_ctor_set(x_8, 5, x_46);
x_47 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_4, x_2, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_59 = lean_ctor_get(x_8, 0);
x_60 = lean_ctor_get(x_8, 1);
x_61 = lean_ctor_get(x_8, 2);
x_62 = lean_ctor_get(x_8, 3);
x_63 = lean_ctor_get(x_8, 4);
x_64 = lean_ctor_get(x_8, 5);
x_65 = lean_ctor_get(x_8, 6);
x_66 = lean_ctor_get(x_8, 7);
x_67 = lean_ctor_get(x_8, 8);
x_68 = lean_ctor_get(x_8, 9);
x_69 = lean_ctor_get(x_8, 10);
x_70 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_71 = lean_ctor_get(x_8, 11);
x_72 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_71);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_8);
x_73 = l_Lean_replaceRef(x_1, x_64);
lean_dec(x_64);
x_74 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_74, 0, x_59);
lean_ctor_set(x_74, 1, x_60);
lean_ctor_set(x_74, 2, x_61);
lean_ctor_set(x_74, 3, x_62);
lean_ctor_set(x_74, 4, x_63);
lean_ctor_set(x_74, 5, x_73);
lean_ctor_set(x_74, 6, x_65);
lean_ctor_set(x_74, 7, x_66);
lean_ctor_set(x_74, 8, x_67);
lean_ctor_set(x_74, 9, x_68);
lean_ctor_set(x_74, 10, x_69);
lean_ctor_set(x_74, 11, x_71);
lean_ctor_set_uint8(x_74, sizeof(void*)*12, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*12 + 1, x_72);
x_75 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_4, x_2, x_11, x_6, x_7, x_74, x_9, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
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
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_76);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_75, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_83 = x_75;
} else {
 lean_dec_ref(x_75);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
case 1:
{
uint8_t x_85; 
lean_dec(x_7);
lean_dec(x_6);
x_85 = !lean_is_exclusive(x_8);
if (x_85 == 0)
{
uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get_uint8(x_5, 0);
x_87 = lean_ctor_get(x_8, 5);
x_88 = l_Lean_replaceRef(x_1, x_87);
lean_dec(x_87);
lean_ctor_set(x_8, 5, x_88);
lean_inc(x_2);
x_89 = l_Lean_Meta_Grind_validateCasesAttr(x_2, x_86, x_8, x_9, x_10);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
x_92 = !lean_is_exclusive(x_4);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_4, 2);
x_94 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_93, x_2, x_86);
lean_ctor_set(x_4, 2, x_94);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_4);
lean_ctor_set(x_89, 0, x_95);
return x_89;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_4, 0);
x_97 = lean_ctor_get(x_4, 1);
x_98 = lean_ctor_get(x_4, 2);
x_99 = lean_ctor_get(x_4, 3);
x_100 = lean_ctor_get(x_4, 4);
x_101 = lean_ctor_get(x_4, 5);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_4);
x_102 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_98, x_2, x_86);
x_103 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_103, 0, x_96);
lean_ctor_set(x_103, 1, x_97);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_99);
lean_ctor_set(x_103, 4, x_100);
lean_ctor_set(x_103, 5, x_101);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_89, 0, x_104);
return x_89;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_105 = lean_ctor_get(x_89, 1);
lean_inc(x_105);
lean_dec(x_89);
x_106 = lean_ctor_get(x_4, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_4, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_4, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_4, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_4, 4);
lean_inc(x_110);
x_111 = lean_ctor_get(x_4, 5);
lean_inc(x_111);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_112 = x_4;
} else {
 lean_dec_ref(x_4);
 x_112 = lean_box(0);
}
x_113 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_108, x_2, x_86);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 6, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_109);
lean_ctor_set(x_114, 4, x_110);
lean_ctor_set(x_114, 5, x_111);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_105);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_4);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_89);
if (x_117 == 0)
{
return x_89;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_89, 0);
x_119 = lean_ctor_get(x_89, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_89);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_121 = lean_ctor_get_uint8(x_5, 0);
x_122 = lean_ctor_get(x_8, 0);
x_123 = lean_ctor_get(x_8, 1);
x_124 = lean_ctor_get(x_8, 2);
x_125 = lean_ctor_get(x_8, 3);
x_126 = lean_ctor_get(x_8, 4);
x_127 = lean_ctor_get(x_8, 5);
x_128 = lean_ctor_get(x_8, 6);
x_129 = lean_ctor_get(x_8, 7);
x_130 = lean_ctor_get(x_8, 8);
x_131 = lean_ctor_get(x_8, 9);
x_132 = lean_ctor_get(x_8, 10);
x_133 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_134 = lean_ctor_get(x_8, 11);
x_135 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_134);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_8);
x_136 = l_Lean_replaceRef(x_1, x_127);
lean_dec(x_127);
x_137 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_123);
lean_ctor_set(x_137, 2, x_124);
lean_ctor_set(x_137, 3, x_125);
lean_ctor_set(x_137, 4, x_126);
lean_ctor_set(x_137, 5, x_136);
lean_ctor_set(x_137, 6, x_128);
lean_ctor_set(x_137, 7, x_129);
lean_ctor_set(x_137, 8, x_130);
lean_ctor_set(x_137, 9, x_131);
lean_ctor_set(x_137, 10, x_132);
lean_ctor_set(x_137, 11, x_134);
lean_ctor_set_uint8(x_137, sizeof(void*)*12, x_133);
lean_ctor_set_uint8(x_137, sizeof(void*)*12 + 1, x_135);
lean_inc(x_2);
x_138 = l_Lean_Meta_Grind_validateCasesAttr(x_2, x_121, x_137, x_9, x_10);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_4, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_4, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_4, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_4, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_4, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_4, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_147 = x_4;
} else {
 lean_dec_ref(x_4);
 x_147 = lean_box(0);
}
x_148 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_143, x_2, x_121);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_141);
lean_ctor_set(x_149, 1, x_142);
lean_ctor_set(x_149, 2, x_148);
lean_ctor_set(x_149, 3, x_144);
lean_ctor_set(x_149, 4, x_145);
lean_ctor_set(x_149, 5, x_146);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
if (lean_is_scalar(x_140)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_140;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_139);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_4);
lean_dec(x_2);
x_152 = lean_ctor_get(x_138, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_138, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_154 = x_138;
} else {
 lean_dec_ref(x_138);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
case 2:
{
uint8_t x_156; lean_object* x_157; 
x_156 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_157 = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(x_2, x_156, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
lean_dec(x_4);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_MessageData_ofName(x_2);
x_161 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__2;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
x_163 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__4;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_164, x_6, x_7, x_8, x_9, x_159);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_165);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
else
{
lean_object* x_170; uint8_t x_171; 
lean_dec(x_2);
x_170 = lean_ctor_get(x_157, 1);
lean_inc(x_170);
lean_dec(x_157);
x_171 = !lean_is_exclusive(x_158);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_158, 0);
x_173 = lean_ctor_get(x_172, 4);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_box(0);
lean_inc(x_173);
x_175 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__3(x_1, x_173, x_174, x_173, x_173, x_4, lean_box(0), x_6, x_7, x_8, x_9, x_170);
lean_dec(x_8);
lean_dec(x_173);
if (lean_obj_tag(x_175) == 0)
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_175, 0);
lean_ctor_set(x_158, 0, x_177);
lean_ctor_set(x_175, 0, x_158);
return x_175;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_175, 0);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_175);
lean_ctor_set(x_158, 0, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_158);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
else
{
uint8_t x_181; 
lean_free_object(x_158);
x_181 = !lean_is_exclusive(x_175);
if (x_181 == 0)
{
return x_175;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_175, 0);
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_175);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = lean_ctor_get(x_158, 0);
lean_inc(x_185);
lean_dec(x_158);
x_186 = lean_ctor_get(x_185, 4);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_box(0);
lean_inc(x_186);
x_188 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__3(x_1, x_186, x_187, x_186, x_186, x_4, lean_box(0), x_6, x_7, x_8, x_9, x_170);
lean_dec(x_8);
lean_dec(x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_189);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_157);
if (x_198 == 0)
{
return x_157;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_157, 0);
x_200 = lean_ctor_get(x_157, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_157);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
default: 
{
uint8_t x_202; lean_object* x_203; 
x_202 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_203 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_2, x_202, x_8, x_9, x_10);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = !lean_is_exclusive(x_8);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_8, 5);
x_208 = l_Lean_replaceRef(x_1, x_207);
lean_dec(x_207);
lean_ctor_set(x_8, 5, x_208);
x_209 = 8;
x_210 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_4, x_2, x_209, x_6, x_7, x_8, x_9, x_205);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_210, 0, x_213);
return x_210;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_210, 0);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_210);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_214);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_210);
if (x_218 == 0)
{
return x_210;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_210, 0);
x_220 = lean_ctor_get(x_210, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_210);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; 
x_222 = lean_ctor_get(x_8, 0);
x_223 = lean_ctor_get(x_8, 1);
x_224 = lean_ctor_get(x_8, 2);
x_225 = lean_ctor_get(x_8, 3);
x_226 = lean_ctor_get(x_8, 4);
x_227 = lean_ctor_get(x_8, 5);
x_228 = lean_ctor_get(x_8, 6);
x_229 = lean_ctor_get(x_8, 7);
x_230 = lean_ctor_get(x_8, 8);
x_231 = lean_ctor_get(x_8, 9);
x_232 = lean_ctor_get(x_8, 10);
x_233 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_234 = lean_ctor_get(x_8, 11);
x_235 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_234);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_8);
x_236 = l_Lean_replaceRef(x_1, x_227);
lean_dec(x_227);
x_237 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_237, 0, x_222);
lean_ctor_set(x_237, 1, x_223);
lean_ctor_set(x_237, 2, x_224);
lean_ctor_set(x_237, 3, x_225);
lean_ctor_set(x_237, 4, x_226);
lean_ctor_set(x_237, 5, x_236);
lean_ctor_set(x_237, 6, x_228);
lean_ctor_set(x_237, 7, x_229);
lean_ctor_set(x_237, 8, x_230);
lean_ctor_set(x_237, 9, x_231);
lean_ctor_set(x_237, 10, x_232);
lean_ctor_set(x_237, 11, x_234);
lean_ctor_set_uint8(x_237, sizeof(void*)*12, x_233);
lean_ctor_set_uint8(x_237, sizeof(void*)*12 + 1, x_235);
x_238 = 8;
x_239 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_4, x_2, x_238, x_6, x_7, x_237, x_9, x_205);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_242 = x_239;
} else {
 lean_dec_ref(x_239);
 x_242 = lean_box(0);
}
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_240);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_239, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_239, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_247 = x_239;
} else {
 lean_dec_ref(x_239);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; uint8_t x_250; 
lean_dec(x_2);
x_249 = lean_ctor_get(x_203, 1);
lean_inc(x_249);
lean_dec(x_203);
x_250 = !lean_is_exclusive(x_204);
if (x_250 == 0)
{
uint8_t x_251; 
x_251 = !lean_is_exclusive(x_4);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_204, 0);
x_253 = lean_ctor_get(x_4, 2);
lean_inc(x_252);
x_254 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_253, x_252, x_202);
lean_ctor_set(x_4, 2, x_254);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_255 = l_Lean_Meta_isInductivePredicate_x3f(x_252, x_6, x_7, x_8, x_9, x_249);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_257 = !lean_is_exclusive(x_255);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_255, 0);
lean_dec(x_258);
lean_ctor_set(x_204, 0, x_4);
lean_ctor_set(x_255, 0, x_204);
return x_255;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
lean_ctor_set(x_204, 0, x_4);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_204);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
else
{
lean_object* x_261; uint8_t x_262; 
lean_free_object(x_204);
x_261 = lean_ctor_get(x_255, 1);
lean_inc(x_261);
lean_dec(x_255);
x_262 = !lean_is_exclusive(x_256);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_256, 0);
x_264 = lean_ctor_get(x_263, 4);
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_box(0);
lean_inc(x_264);
x_266 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4(x_1, x_264, x_265, x_264, x_264, x_4, lean_box(0), x_6, x_7, x_8, x_9, x_261);
lean_dec(x_8);
lean_dec(x_264);
if (lean_obj_tag(x_266) == 0)
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_266, 0);
lean_ctor_set(x_256, 0, x_268);
lean_ctor_set(x_266, 0, x_256);
return x_266;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_266, 0);
x_270 = lean_ctor_get(x_266, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_266);
lean_ctor_set(x_256, 0, x_269);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_256);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
else
{
uint8_t x_272; 
lean_free_object(x_256);
x_272 = !lean_is_exclusive(x_266);
if (x_272 == 0)
{
return x_266;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_266, 0);
x_274 = lean_ctor_get(x_266, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_266);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_256, 0);
lean_inc(x_276);
lean_dec(x_256);
x_277 = lean_ctor_get(x_276, 4);
lean_inc(x_277);
lean_dec(x_276);
x_278 = lean_box(0);
lean_inc(x_277);
x_279 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4(x_1, x_277, x_278, x_277, x_277, x_4, lean_box(0), x_6, x_7, x_8, x_9, x_261);
lean_dec(x_8);
lean_dec(x_277);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_282 = x_279;
} else {
 lean_dec_ref(x_279);
 x_282 = lean_box(0);
}
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_280);
if (lean_is_scalar(x_282)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_282;
}
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_281);
return x_284;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_279, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_279, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_287 = x_279;
} else {
 lean_dec_ref(x_279);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_4);
lean_free_object(x_204);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_289 = !lean_is_exclusive(x_255);
if (x_289 == 0)
{
return x_255;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_255, 0);
x_291 = lean_ctor_get(x_255, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_255);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_293 = lean_ctor_get(x_204, 0);
x_294 = lean_ctor_get(x_4, 0);
x_295 = lean_ctor_get(x_4, 1);
x_296 = lean_ctor_get(x_4, 2);
x_297 = lean_ctor_get(x_4, 3);
x_298 = lean_ctor_get(x_4, 4);
x_299 = lean_ctor_get(x_4, 5);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_4);
lean_inc(x_293);
x_300 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_296, x_293, x_202);
x_301 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_301, 0, x_294);
lean_ctor_set(x_301, 1, x_295);
lean_ctor_set(x_301, 2, x_300);
lean_ctor_set(x_301, 3, x_297);
lean_ctor_set(x_301, 4, x_298);
lean_ctor_set(x_301, 5, x_299);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_302 = l_Lean_Meta_isInductivePredicate_x3f(x_293, x_6, x_7, x_8, x_9, x_249);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_305 = x_302;
} else {
 lean_dec_ref(x_302);
 x_305 = lean_box(0);
}
lean_ctor_set(x_204, 0, x_301);
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_204);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_free_object(x_204);
x_307 = lean_ctor_get(x_302, 1);
lean_inc(x_307);
lean_dec(x_302);
x_308 = lean_ctor_get(x_303, 0);
lean_inc(x_308);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_309 = x_303;
} else {
 lean_dec_ref(x_303);
 x_309 = lean_box(0);
}
x_310 = lean_ctor_get(x_308, 4);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_box(0);
lean_inc(x_310);
x_312 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4(x_1, x_310, x_311, x_310, x_310, x_301, lean_box(0), x_6, x_7, x_8, x_9, x_307);
lean_dec(x_8);
lean_dec(x_310);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_315 = x_312;
} else {
 lean_dec_ref(x_312);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_316 = x_309;
}
lean_ctor_set(x_316, 0, x_313);
if (lean_is_scalar(x_315)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_315;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_314);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_309);
x_318 = lean_ctor_get(x_312, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_312, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_320 = x_312;
} else {
 lean_dec_ref(x_312);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_301);
lean_free_object(x_204);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_322 = lean_ctor_get(x_302, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_302, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 lean_ctor_release(x_302, 1);
 x_324 = x_302;
} else {
 lean_dec_ref(x_302);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_326 = lean_ctor_get(x_204, 0);
lean_inc(x_326);
lean_dec(x_204);
x_327 = lean_ctor_get(x_4, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_4, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_4, 2);
lean_inc(x_329);
x_330 = lean_ctor_get(x_4, 3);
lean_inc(x_330);
x_331 = lean_ctor_get(x_4, 4);
lean_inc(x_331);
x_332 = lean_ctor_get(x_4, 5);
lean_inc(x_332);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 x_333 = x_4;
} else {
 lean_dec_ref(x_4);
 x_333 = lean_box(0);
}
lean_inc(x_326);
x_334 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_329, x_326, x_202);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 6, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_327);
lean_ctor_set(x_335, 1, x_328);
lean_ctor_set(x_335, 2, x_334);
lean_ctor_set(x_335, 3, x_330);
lean_ctor_set(x_335, 4, x_331);
lean_ctor_set(x_335, 5, x_332);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_336 = l_Lean_Meta_isInductivePredicate_x3f(x_326, x_6, x_7, x_8, x_9, x_249);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_339 = x_336;
} else {
 lean_dec_ref(x_336);
 x_339 = lean_box(0);
}
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_335);
if (lean_is_scalar(x_339)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_339;
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_338);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_342 = lean_ctor_get(x_336, 1);
lean_inc(x_342);
lean_dec(x_336);
x_343 = lean_ctor_get(x_337, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_344 = x_337;
} else {
 lean_dec_ref(x_337);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_343, 4);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_box(0);
lean_inc(x_345);
x_347 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4(x_1, x_345, x_346, x_345, x_345, x_335, lean_box(0), x_6, x_7, x_8, x_9, x_342);
lean_dec(x_8);
lean_dec(x_345);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
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
if (lean_is_scalar(x_344)) {
 x_351 = lean_alloc_ctor(1, 1, 0);
} else {
 x_351 = x_344;
}
lean_ctor_set(x_351, 0, x_348);
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_349);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_344);
x_353 = lean_ctor_get(x_347, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_347, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_355 = x_347;
} else {
 lean_dec_ref(x_347);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_335);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_357 = lean_ctor_get(x_336, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_336, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 x_359 = x_336;
} else {
 lean_dec_ref(x_336);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_361 = !lean_is_exclusive(x_203);
if (x_361 == 0)
{
return x_203;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_203, 0);
x_363 = lean_ctor_get(x_203, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_203);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Tactic_elabGrindPattern___closed__6;
lean_inc(x_13);
x_15 = l_Lean_Syntax_isOfKind(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_3);
x_16 = l_Lean_MessageData_ofSyntax(x_2);
x_17 = l_Lean_indentD(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_21, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_28 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_13, x_27, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(3);
x_32 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3(x_2, x_29, x_4, x_3, x_31, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_ctor_get(x_6, 0);
lean_inc(x_35);
lean_dec(x_6);
x_36 = l_Lean_Meta_Grind_getAttrKindCore(x_35, x_9, x_10, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3(x_2, x_33, x_4, x_3, x_37, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_37);
lean_dec(x_2);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_28, 0);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_28);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindParam", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindErase", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLemma", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Attr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindMod", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; uint8_t x_26; 
x_15 = lean_array_uget(x_4, x_6);
x_25 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
lean_inc(x_15);
x_26 = l_Lean_Syntax_isOfKind(x_15, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_7);
x_27 = l_Lean_MessageData_ofSyntax(x_15);
x_28 = l_Lean_indentD(x_27);
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_32, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_15, x_38);
x_40 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__4;
lean_inc(x_39);
x_41 = l_Lean_Syntax_isOfKind(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_39);
x_43 = l_Lean_Syntax_isOfKind(x_39, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_39);
lean_dec(x_7);
x_44 = l_Lean_MessageData_ofSyntax(x_15);
x_45 = l_Lean_indentD(x_44);
x_46 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_49, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Syntax_getArg(x_39, x_38);
x_56 = l_Lean_Syntax_isNone(x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_unsigned_to_nat(1u);
lean_inc(x_55);
x_58 = l_Lean_Syntax_matchesNull(x_55, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_55);
lean_dec(x_39);
lean_dec(x_7);
x_59 = l_Lean_MessageData_ofSyntax(x_15);
x_60 = l_Lean_indentD(x_59);
x_61 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_64, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = l_Lean_Syntax_getArg(x_55, x_38);
lean_dec(x_55);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_70);
x_72 = l_Lean_Syntax_isOfKind(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_39);
lean_dec(x_7);
x_73 = l_Lean_MessageData_ofSyntax(x_15);
x_74 = l_Lean_indentD(x_73);
x_75 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_78, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_70);
x_85 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_86 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4(x_39, x_15, x_7, x_2, x_85, x_84, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_39);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_16 = x_87;
x_17 = x_88;
goto block_24;
}
else
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_55);
x_93 = lean_box(0);
x_94 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_95 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4(x_39, x_15, x_7, x_2, x_94, x_93, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_39);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_16 = x_96;
x_17 = x_97;
goto block_24;
}
else
{
uint8_t x_98; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_98 = !lean_is_exclusive(x_95);
if (x_98 == 0)
{
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_95);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_unsigned_to_nat(1u);
x_103 = l_Lean_Syntax_getArg(x_39, x_102);
lean_dec(x_39);
x_104 = l_Lean_Elab_Tactic_elabGrindPattern___closed__6;
lean_inc(x_103);
x_105 = l_Lean_Syntax_isOfKind(x_103, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_103);
lean_dec(x_7);
x_106 = l_Lean_MessageData_ofSyntax(x_15);
x_107 = l_Lean_indentD(x_106);
x_108 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2;
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_111, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
return x_112;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_112);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_15);
x_117 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
x_118 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_103, x_117, x_10, x_11, x_12);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_119);
x_122 = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(x_119, x_121, x_10, x_11, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = !lean_is_exclusive(x_7);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_7, 0);
x_127 = lean_ctor_get(x_7, 1);
x_128 = lean_ctor_get(x_7, 2);
x_129 = lean_ctor_get(x_7, 3);
x_130 = lean_ctor_get(x_7, 4);
x_131 = lean_ctor_get(x_7, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_132 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_127, x_119, x_8, x_9, x_10, x_11, x_124);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_ctor_set(x_7, 1, x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_7);
x_16 = x_135;
x_17 = x_134;
goto block_24;
}
else
{
uint8_t x_136; 
lean_free_object(x_7);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
return x_132;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_132, 0);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_132);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_7, 0);
x_141 = lean_ctor_get(x_7, 1);
x_142 = lean_ctor_get(x_7, 2);
x_143 = lean_ctor_get(x_7, 3);
x_144 = lean_ctor_get(x_7, 4);
x_145 = lean_ctor_get(x_7, 5);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_146 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_141, x_119, x_8, x_9, x_10, x_11, x_124);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_149, 0, x_140);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_142);
lean_ctor_set(x_149, 3, x_143);
lean_ctor_set(x_149, 4, x_144);
lean_ctor_set(x_149, 5, x_145);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_16 = x_150;
x_17 = x_148;
goto block_24;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_151 = lean_ctor_get(x_146, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_153 = x_146;
} else {
 lean_dec_ref(x_146);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_119);
x_155 = lean_ctor_get(x_122, 1);
lean_inc(x_155);
lean_dec(x_122);
x_156 = !lean_is_exclusive(x_123);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_123, 0);
lean_inc(x_157);
x_158 = l_Lean_Meta_Grind_ensureNotBuiltinCases(x_157, x_10, x_11, x_155);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_160 = !lean_is_exclusive(x_7);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_7, 0);
x_162 = lean_ctor_get(x_7, 1);
x_163 = lean_ctor_get(x_7, 2);
x_164 = lean_ctor_get(x_7, 3);
x_165 = lean_ctor_get(x_7, 4);
x_166 = lean_ctor_get(x_7, 5);
x_167 = l_Lean_Meta_Grind_CasesTypes_eraseDecl(x_163, x_157, x_10, x_11, x_159);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_ctor_set(x_7, 2, x_168);
lean_ctor_set(x_123, 0, x_7);
x_16 = x_123;
x_17 = x_169;
goto block_24;
}
else
{
uint8_t x_170; 
lean_free_object(x_7);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_161);
lean_free_object(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_170 = !lean_is_exclusive(x_167);
if (x_170 == 0)
{
return x_167;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_167, 0);
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_167);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_7, 0);
x_175 = lean_ctor_get(x_7, 1);
x_176 = lean_ctor_get(x_7, 2);
x_177 = lean_ctor_get(x_7, 3);
x_178 = lean_ctor_get(x_7, 4);
x_179 = lean_ctor_get(x_7, 5);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_7);
x_180 = l_Lean_Meta_Grind_CasesTypes_eraseDecl(x_176, x_157, x_10, x_11, x_159);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_175);
lean_ctor_set(x_183, 2, x_181);
lean_ctor_set(x_183, 3, x_177);
lean_ctor_set(x_183, 4, x_178);
lean_ctor_set(x_183, 5, x_179);
lean_ctor_set(x_123, 0, x_183);
x_16 = x_123;
x_17 = x_182;
goto block_24;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_186 = x_180;
} else {
 lean_dec_ref(x_180);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_free_object(x_123);
lean_dec(x_157);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_188 = !lean_is_exclusive(x_158);
if (x_188 == 0)
{
return x_158;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_158, 0);
x_190 = lean_ctor_get(x_158, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_158);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_123, 0);
lean_inc(x_192);
lean_dec(x_123);
lean_inc(x_192);
x_193 = l_Lean_Meta_Grind_ensureNotBuiltinCases(x_192, x_10, x_11, x_155);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_ctor_get(x_7, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_7, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_7, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_7, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_7, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_7, 5);
lean_inc(x_200);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_201 = x_7;
} else {
 lean_dec_ref(x_7);
 x_201 = lean_box(0);
}
x_202 = l_Lean_Meta_Grind_CasesTypes_eraseDecl(x_197, x_192, x_10, x_11, x_194);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(0, 6, 0);
} else {
 x_205 = x_201;
}
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_196);
lean_ctor_set(x_205, 2, x_203);
lean_ctor_set(x_205, 3, x_198);
lean_ctor_set(x_205, 4, x_199);
lean_ctor_set(x_205, 5, x_200);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_16 = x_206;
x_17 = x_204;
goto block_24;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_207 = lean_ctor_get(x_202, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_202, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_209 = x_202;
} else {
 lean_dec_ref(x_202);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_192);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_211 = lean_ctor_get(x_193, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_193, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_213 = x_193;
} else {
 lean_dec_ref(x_193);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_119);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_215 = !lean_is_exclusive(x_122);
if (x_215 == 0)
{
return x_122;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_122, 0);
x_217 = lean_ctor_get(x_122, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_122);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_219 = !lean_is_exclusive(x_118);
if (x_219 == 0)
{
return x_118;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_118, 0);
x_221 = lean_ctor_get(x_118, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_118);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_7 = x_20;
x_12 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5(x_2, x_3, x_9, x_2, x_10, x_11, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
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
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5(x_1, x_13, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Elab_Tactic_elabGrindParams(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
lean_ctor_set(x_1, 2, x_5);
lean_ctor_set(x_1, 1, x_2);
x_14 = l_Lean_Elab_Tactic_elabGrindParams(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 2, x_5);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
x_20 = l_Lean_Elab_Tactic_elabGrindParams(x_19, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_3 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_Grind_getCasesTypes___rarg(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_mkGrindParams___lambda__1(x_1, x_4, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2;
x_15 = l_Lean_Elab_Tactic_mkGrindParams___lambda__1(x_1, x_4, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkGrindParams___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_mkParams(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
if (x_2 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Grind_getEMatchTheorems___rarg(x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2(x_10, x_3, x_2, x_13, x_4, x_5, x_6, x_7, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Lean_Elab_Tactic_mkGrindParams___closed__1;
x_19 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2(x_16, x_3, x_2, x_18, x_4, x_5, x_6, x_7, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Elab_Tactic_mkGrindParams___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Elab_Tactic_mkGrindParams(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`grind` failed\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_grind___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Elab_Tactic_mkGrindParams(x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
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
x_15 = l_Lean_Meta_Grind_main(x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_Result_hasFailures(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Tactic_grind___lambda__1(x_16, x_19, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_16);
return x_20;
}
else
{
lean_object* x_21; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_Grind_Result_toMessageData(x_16, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Tactic_grind___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_27, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
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
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
return x_12;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_grind___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_Tactic_grind(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Lean_stringToMessageData(x_9);
x_11 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_eval_const(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___rarg), 1, 0);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GoalM", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__2;
x_3 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2;
x_4 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__5;
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__8;
x_3 = l_Lean_Expr_app___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__12() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__11;
x_3 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10;
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2;
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__12;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_grind_fallback", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_box(0);
x_14 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15;
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize), 9, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13;
x_17 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__3___rarg(x_16, x_17, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16;
if (lean_obj_tag(x_19) == 4)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_1);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_apply_8(x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18;
lean_inc(x_2);
x_25 = l_Lean_Elab_Term_mkAuxName(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9;
lean_inc(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_13);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_13);
x_31 = lean_box(0);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_19);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
lean_ctor_set(x_1, 0, x_33);
lean_inc(x_7);
lean_inc(x_6);
x_34 = l_Lean_addAndCompile(x_1, x_6, x_7, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_apply_8(x_21, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
return x_18;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_18, 0);
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_18);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15;
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermAndSynthesize), 9, 2);
lean_closure_set(x_52, 0, x_49);
lean_closure_set(x_52, 1, x_51);
x_53 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13;
x_54 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_55 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__3___rarg(x_53, x_54, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16;
if (lean_obj_tag(x_56) == 4)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_apply_8(x_58, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18;
lean_inc(x_2);
x_62 = l_Lean_Elab_Term_mkAuxName(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9;
lean_inc(x_63);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_50);
lean_ctor_set(x_66, 2, x_65);
lean_inc(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_50);
x_68 = lean_box(0);
x_69 = 1;
x_70 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_56);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_inc(x_7);
lean_inc(x_6);
x_72 = l_Lean_addAndCompile(x_71, x_6, x_7, x_64);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_apply_8(x_58, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_73);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_77 = x_72;
} else {
 lean_dec_ref(x_72);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_ctor_get(x_62, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_81 = x_62;
} else {
 lean_dec_ref(x_62);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_55, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_55, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_85 = x_55;
} else {
 lean_dec_ref(x_55);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_Elab_Tactic_grind(x_16, x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Tactic_replaceMainGoal(x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_19);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_grind", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Elab_Term_getDeclName_x3f(x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__2;
x_19 = lean_box(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrindCore___lambda__1___boxed), 14, 5);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_18);
lean_closure_set(x_20, 4, x_4);
x_21 = l_Lean_Elab_Tactic_withMainContext___rarg(x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_box(x_2);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrindCore___lambda__1___boxed), 14, 5);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_23);
lean_closure_set(x_25, 4, x_4);
x_26 = l_Lean_Elab_Tactic_withMainContext___rarg(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_grind_warning;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `grind` tactic is experimental and still under development. Avoid using it in production projects", 101, 101);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalGrindCore___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalGrindCore___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
x_19 = l_Lean_Elab_Tactic_evalGrindCore___closed__1;
x_20 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_18, x_19);
lean_dec(x_18);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_36; 
x_36 = 0;
x_21 = x_36;
goto block_35;
}
else
{
uint8_t x_37; 
x_37 = 1;
x_21 = x_37;
goto block_35;
}
block_35:
{
lean_object* x_22; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_32; 
x_32 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
x_22 = x_32;
goto block_31;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = l_Lean_Syntax_TSepArray_getElems___rarg(x_33);
x_22 = x_34;
goto block_31;
}
block_31:
{
if (x_20 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_evalGrindCore___lambda__2(x_2, x_21, x_22, x_16, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = l_Lean_Elab_Tactic_evalGrindCore___closed__4;
x_26 = 1;
lean_inc(x_12);
x_27 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_1, x_25, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Tactic_evalGrindCore___lambda__2(x_2, x_21, x_22, x_16, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
lean_dec(x_28);
return x_30;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Lean_Elab_Tactic_evalGrindCore___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Lean_Elab_Tactic_evalGrindCore___lambda__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalGrindCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grindParamsPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(3u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_grindOnlyPos() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isGrindOnly___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_isGrindOnly___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_isGrindOnly(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_Elab_Tactic_grindOnlyPos;
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
lean_dec(x_1);
x_8 = l_Lean_Syntax_isNone(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_isGrindOnly___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_isGrindOnly(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_setGrindParams___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_setGrindParams___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_setGrindParams___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_setGrindParams___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_setGrindParams___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_setGrindParams___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_3 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___rarg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = l_Lean_Elab_Tactic_setGrindParams___closed__4;
x_5 = l_Lean_Syntax_mkSep(x_2, x_4);
x_6 = l_Lean_Elab_Tactic_setGrindParams___closed__7;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Elab_Tactic_setGrindParams___closed__2;
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_array_mk(x_9);
x_11 = lean_box(2);
x_12 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
x_14 = l_Lean_Elab_Tactic_grindParamsPos;
x_15 = l_Lean_Syntax_setArg(x_1, x_14, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_Tactic_grindParamsPos;
x_17 = l_Lean_Elab_Tactic_setGrindParams___closed__10;
x_18 = l_Lean_Syntax_setArg(x_1, x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_setGrindParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_setGrindParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_grindParamsPos;
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_3, x_4);
lean_dec(x_3);
x_6 = l_Lean_Syntax_getSepArgs(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_getGrindParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getGrindParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__4(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_20 = l_Lean_resolveGlobalName___at___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin___spec__4(x_19, x_9, x_10, x_11, x_12, x_13);
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
x_65 = l_Lean_resolveGlobalName___at___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin___spec__4(x_64, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_Name_componentsRev(x_1);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___closed__1;
lean_inc(x_9);
x_13 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__8(x_2, x_9, x_10, x_11, x_9, x_9, x_12, lean_box(0), x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Name_hasMacroScopes(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2(x_2, x_1, x_9, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_17 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7(x_1, x_16, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_mkGrindOnly___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Name_getPrefix(x_7);
x_9 = l_Lean_Name_getPrefix(x_1);
x_10 = l_Lean_Name_isPrefixOf(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
return x_5;
}
}
}
static lean_object* _init_l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_rootNamespace;
lean_inc(x_1);
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = lean_array_push(x_2, x_10);
x_12 = lean_box(0);
x_13 = lean_array_size(x_11);
x_14 = 0;
x_15 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___closed__1;
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__9(x_1, x_11, x_12, x_15, x_11, x_13, x_14, x_15, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_Lean_getRevAliases(x_12, x_1);
x_14 = lean_array_mk(x_13);
if (x_2 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_18 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
x_19 = lean_box(0);
x_20 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1(x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_11);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_15, x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_14);
x_22 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
x_23 = lean_box(0);
x_24 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1(x_1, x_22, x_23, x_4, x_5, x_6, x_7, x_11);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_27 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_mkGrindOnly___spec__10(x_1, x_14, x_25, x_26, x_27);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1(x_1, x_28, x_29, x_4, x_5, x_6, x_7, x_11);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1(x_1, x_14, x_31, x_4, x_5, x_6, x_7, x_11);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__3(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__2(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_12 = l_Lean_resolveGlobalName___at___private_Lean_Meta_Tactic_Grind_PropagatorAttr_0__Lean_Meta_Grind_addBuiltin___spec__4(x_2, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
lean_inc(x_22);
x_23 = lean_private_to_user_name(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = lean_name_eq(x_22, x_2);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_rootNamespace;
x_26 = l_Lean_Name_append(x_25, x_2);
lean_ctor_set(x_12, 0, x_26);
return x_12;
}
else
{
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_name_eq(x_27, x_2);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_rootNamespace;
x_30 = l_Lean_Name_append(x_29, x_2);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_18, 0);
lean_inc(x_32);
lean_dec(x_18);
lean_inc(x_32);
x_33 = lean_private_to_user_name(x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = lean_name_eq(x_32, x_2);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lean_rootNamespace;
x_36 = l_Lean_Name_append(x_35, x_2);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_2);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_32);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_name_eq(x_39, x_2);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = l_Lean_rootNamespace;
x_42 = l_Lean_Name_append(x_41, x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_31);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_19);
lean_dec(x_18);
x_45 = !lean_is_exclusive(x_12);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_12, 0);
lean_dec(x_46);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_12, 1);
lean_inc(x_47);
lean_dec(x_12);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Name_hasMacroScopes(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__3(x_2, x_1, x_3, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
static lean_object* _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_root_", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_11 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__2;
x_12 = l_Lean_Name_append(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_8 = 0;
lean_inc(x_5);
lean_inc(x_1);
x_9 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = l_Lean_LocalContext_usesUserName(x_13, x_11);
if (x_14 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_15 = lean_box(0);
x_16 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1(x_11, x_1, x_15, x_3, x_4, x_5, x_6, x_12);
lean_dec(x_5);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_ctor_get(x_3, 2);
x_20 = l_Lean_LocalContext_usesUserName(x_19, x_17);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1(x_17, x_1, x_22, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_5);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_push(x_2, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEqRhs", 10, 10);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEqBoth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindEqBwd", 10, 10);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__9;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("←", 3, 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindFwd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("→ ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16;
x_2 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__17;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("→", 3, 1);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindBwd", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__20;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16;
x_2 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__22;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLR", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__24;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=> ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16;
x_2 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__26;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("=>", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindRL", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__29;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<= ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16;
x_2 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__31;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<=", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindUsr", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__34;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("usr", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
switch (lean_obj_tag(x_22)) {
case 0:
{
uint8_t x_23; uint8_t x_24; 
lean_free_object(x_4);
x_23 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_st_ref_get(x_10, x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Match_isMatchEqnTheorem(x_33, x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_29);
lean_free_object(x_22);
x_35 = l_Lean_Meta_isEqnThm_x3f(x_28, x_9, x_10, x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_5);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 0;
lean_inc(x_9);
x_39 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_28, x_38, x_7, x_8, x_9, x_10, x_37);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_mk_syntax_ident(x_41);
switch (x_23) {
case 0:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_39);
x_44 = lean_ctor_get(x_9, 5);
lean_inc(x_44);
x_45 = l_Lean_SourceInfo_fromRef(x_44, x_38);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_10, x_42);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_48 = lean_ctor_get(x_46, 1);
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_45);
lean_ctor_set_tag(x_46, 2);
lean_ctor_set(x_46, 1, x_50);
lean_ctor_set(x_46, 0, x_45);
x_51 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
lean_inc(x_45);
x_52 = l_Lean_Syntax_node1(x_45, x_51, x_46);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_45);
x_54 = l_Lean_Syntax_node1(x_45, x_53, x_52);
x_55 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_45);
x_56 = l_Lean_Syntax_node1(x_45, x_55, x_54);
x_57 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_45);
x_58 = l_Lean_Syntax_node2(x_45, x_57, x_56, x_43);
x_59 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_60 = l_Lean_Syntax_node1(x_45, x_59, x_58);
x_61 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_60, x_7, x_8, x_9, x_10, x_48);
x_16 = x_61;
goto block_21;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
lean_dec(x_46);
x_63 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_45);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_45);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
lean_inc(x_45);
x_66 = l_Lean_Syntax_node1(x_45, x_65, x_64);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_45);
x_68 = l_Lean_Syntax_node1(x_45, x_67, x_66);
x_69 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_45);
x_70 = l_Lean_Syntax_node1(x_45, x_69, x_68);
x_71 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_45);
x_72 = l_Lean_Syntax_node2(x_45, x_71, x_70, x_43);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_74 = l_Lean_Syntax_node1(x_45, x_73, x_72);
x_75 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_74, x_7, x_8, x_9, x_10, x_62);
x_16 = x_75;
goto block_21;
}
}
case 1:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_9, 5);
lean_inc(x_76);
x_77 = l_Lean_SourceInfo_fromRef(x_76, x_38);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_10, x_42);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_80 = lean_ctor_get(x_78, 1);
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
x_82 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_77);
lean_ctor_set_tag(x_78, 2);
lean_ctor_set(x_78, 1, x_82);
lean_ctor_set(x_78, 0, x_77);
x_83 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_77);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_83);
lean_ctor_set(x_39, 0, x_77);
x_84 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
lean_inc(x_77);
x_85 = l_Lean_Syntax_node2(x_77, x_84, x_78, x_39);
x_86 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_77);
x_87 = l_Lean_Syntax_node1(x_77, x_86, x_85);
x_88 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_77);
x_89 = l_Lean_Syntax_node1(x_77, x_88, x_87);
x_90 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_77);
x_91 = l_Lean_Syntax_node2(x_77, x_90, x_89, x_43);
x_92 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_93 = l_Lean_Syntax_node1(x_77, x_92, x_91);
x_94 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_93, x_7, x_8, x_9, x_10, x_80);
x_16 = x_94;
goto block_21;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_dec(x_78);
x_96 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_77);
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_77);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_98);
lean_ctor_set(x_39, 0, x_77);
x_99 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
lean_inc(x_77);
x_100 = l_Lean_Syntax_node2(x_77, x_99, x_97, x_39);
x_101 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_77);
x_102 = l_Lean_Syntax_node1(x_77, x_101, x_100);
x_103 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_77);
x_104 = l_Lean_Syntax_node1(x_77, x_103, x_102);
x_105 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_77);
x_106 = l_Lean_Syntax_node2(x_77, x_105, x_104, x_43);
x_107 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_108 = l_Lean_Syntax_node1(x_77, x_107, x_106);
x_109 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_108, x_7, x_8, x_9, x_10, x_95);
x_16 = x_109;
goto block_21;
}
}
case 2:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_9, 5);
lean_inc(x_110);
x_111 = l_Lean_SourceInfo_fromRef(x_110, x_38);
lean_dec(x_110);
x_112 = lean_st_ref_get(x_10, x_42);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_114 = lean_ctor_get(x_112, 1);
x_115 = lean_ctor_get(x_112, 0);
lean_dec(x_115);
x_116 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_111);
lean_ctor_set_tag(x_112, 2);
lean_ctor_set(x_112, 1, x_116);
lean_ctor_set(x_112, 0, x_111);
x_117 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_111);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_117);
lean_ctor_set(x_39, 0, x_111);
x_118 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_inc(x_112);
lean_inc(x_111);
x_119 = l_Lean_Syntax_node3(x_111, x_118, x_112, x_39, x_112);
x_120 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_111);
x_121 = l_Lean_Syntax_node1(x_111, x_120, x_119);
x_122 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_111);
x_123 = l_Lean_Syntax_node1(x_111, x_122, x_121);
x_124 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_111);
x_125 = l_Lean_Syntax_node2(x_111, x_124, x_123, x_43);
x_126 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_127 = l_Lean_Syntax_node1(x_111, x_126, x_125);
x_128 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_127, x_7, x_8, x_9, x_10, x_114);
x_16 = x_128;
goto block_21;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_129 = lean_ctor_get(x_112, 1);
lean_inc(x_129);
lean_dec(x_112);
x_130 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_111);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_111);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_111);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_132);
lean_ctor_set(x_39, 0, x_111);
x_133 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_inc(x_131);
lean_inc(x_111);
x_134 = l_Lean_Syntax_node3(x_111, x_133, x_131, x_39, x_131);
x_135 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_111);
x_136 = l_Lean_Syntax_node1(x_111, x_135, x_134);
x_137 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_111);
x_138 = l_Lean_Syntax_node1(x_111, x_137, x_136);
x_139 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_111);
x_140 = l_Lean_Syntax_node2(x_111, x_139, x_138, x_43);
x_141 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_142 = l_Lean_Syntax_node1(x_111, x_141, x_140);
x_143 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_142, x_7, x_8, x_9, x_10, x_129);
x_16 = x_143;
goto block_21;
}
}
case 3:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_9, 5);
lean_inc(x_144);
x_145 = l_Lean_SourceInfo_fromRef(x_144, x_38);
lean_dec(x_144);
x_146 = lean_st_ref_get(x_10, x_42);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_148 = lean_ctor_get(x_146, 1);
x_149 = lean_ctor_get(x_146, 0);
lean_dec(x_149);
x_150 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_145);
lean_ctor_set_tag(x_146, 2);
lean_ctor_set(x_146, 1, x_150);
lean_ctor_set(x_146, 0, x_145);
x_151 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_145);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_151);
lean_ctor_set(x_39, 0, x_145);
x_152 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
lean_inc(x_145);
x_153 = l_Lean_Syntax_node2(x_145, x_152, x_146, x_39);
x_154 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
lean_inc(x_145);
x_155 = l_Lean_Syntax_node1(x_145, x_154, x_153);
x_156 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_145);
x_157 = l_Lean_Syntax_node1(x_145, x_156, x_155);
x_158 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_145);
x_159 = l_Lean_Syntax_node1(x_145, x_158, x_157);
x_160 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_145);
x_161 = l_Lean_Syntax_node2(x_145, x_160, x_159, x_43);
x_162 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_163 = l_Lean_Syntax_node1(x_145, x_162, x_161);
x_164 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_163, x_7, x_8, x_9, x_10, x_148);
x_16 = x_164;
goto block_21;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_165 = lean_ctor_get(x_146, 1);
lean_inc(x_165);
lean_dec(x_146);
x_166 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_145);
x_167 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_167, 0, x_145);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_145);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_168);
lean_ctor_set(x_39, 0, x_145);
x_169 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
lean_inc(x_145);
x_170 = l_Lean_Syntax_node2(x_145, x_169, x_167, x_39);
x_171 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
lean_inc(x_145);
x_172 = l_Lean_Syntax_node1(x_145, x_171, x_170);
x_173 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_145);
x_174 = l_Lean_Syntax_node1(x_145, x_173, x_172);
x_175 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_145);
x_176 = l_Lean_Syntax_node1(x_145, x_175, x_174);
x_177 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_145);
x_178 = l_Lean_Syntax_node2(x_145, x_177, x_176, x_43);
x_179 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_180 = l_Lean_Syntax_node1(x_145, x_179, x_178);
x_181 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_180, x_7, x_8, x_9, x_10, x_165);
x_16 = x_181;
goto block_21;
}
}
case 4:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_free_object(x_39);
x_182 = lean_ctor_get(x_9, 5);
lean_inc(x_182);
x_183 = l_Lean_SourceInfo_fromRef(x_182, x_38);
lean_dec(x_182);
x_184 = lean_st_ref_get(x_10, x_42);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_186 = lean_ctor_get(x_184, 1);
x_187 = lean_ctor_get(x_184, 0);
lean_dec(x_187);
x_188 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
lean_inc(x_183);
lean_ctor_set_tag(x_184, 2);
lean_ctor_set(x_184, 1, x_188);
lean_ctor_set(x_184, 0, x_183);
x_189 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_inc(x_183);
x_190 = l_Lean_Syntax_node1(x_183, x_189, x_184);
x_191 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_inc(x_183);
x_192 = l_Lean_Syntax_node1(x_183, x_191, x_190);
x_193 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_183);
x_194 = l_Lean_Syntax_node1(x_183, x_193, x_192);
x_195 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_183);
x_196 = l_Lean_Syntax_node1(x_183, x_195, x_194);
x_197 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_183);
x_198 = l_Lean_Syntax_node2(x_183, x_197, x_196, x_43);
x_199 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_200 = l_Lean_Syntax_node1(x_183, x_199, x_198);
x_201 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_200, x_7, x_8, x_9, x_10, x_186);
x_16 = x_201;
goto block_21;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_202 = lean_ctor_get(x_184, 1);
lean_inc(x_202);
lean_dec(x_184);
x_203 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
lean_inc(x_183);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_183);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_inc(x_183);
x_206 = l_Lean_Syntax_node1(x_183, x_205, x_204);
x_207 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_inc(x_183);
x_208 = l_Lean_Syntax_node1(x_183, x_207, x_206);
x_209 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_183);
x_210 = l_Lean_Syntax_node1(x_183, x_209, x_208);
x_211 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_183);
x_212 = l_Lean_Syntax_node1(x_183, x_211, x_210);
x_213 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_183);
x_214 = l_Lean_Syntax_node2(x_183, x_213, x_212, x_43);
x_215 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_216 = l_Lean_Syntax_node1(x_183, x_215, x_214);
x_217 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_216, x_7, x_8, x_9, x_10, x_202);
x_16 = x_217;
goto block_21;
}
}
case 5:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
lean_free_object(x_39);
x_218 = lean_ctor_get(x_9, 5);
lean_inc(x_218);
x_219 = l_Lean_SourceInfo_fromRef(x_218, x_38);
lean_dec(x_218);
x_220 = lean_st_ref_get(x_10, x_42);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_222 = lean_ctor_get(x_220, 1);
x_223 = lean_ctor_get(x_220, 0);
lean_dec(x_223);
x_224 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_219);
lean_ctor_set_tag(x_220, 2);
lean_ctor_set(x_220, 1, x_224);
lean_ctor_set(x_220, 0, x_219);
x_225 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
lean_inc(x_219);
x_226 = l_Lean_Syntax_node1(x_219, x_225, x_220);
x_227 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
lean_inc(x_219);
x_228 = l_Lean_Syntax_node1(x_219, x_227, x_226);
x_229 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_219);
x_230 = l_Lean_Syntax_node1(x_219, x_229, x_228);
x_231 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_219);
x_232 = l_Lean_Syntax_node1(x_219, x_231, x_230);
x_233 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_219);
x_234 = l_Lean_Syntax_node2(x_219, x_233, x_232, x_43);
x_235 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_236 = l_Lean_Syntax_node1(x_219, x_235, x_234);
x_237 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_236, x_7, x_8, x_9, x_10, x_222);
x_16 = x_237;
goto block_21;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_238 = lean_ctor_get(x_220, 1);
lean_inc(x_238);
lean_dec(x_220);
x_239 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_219);
x_240 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_240, 0, x_219);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
lean_inc(x_219);
x_242 = l_Lean_Syntax_node1(x_219, x_241, x_240);
x_243 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
lean_inc(x_219);
x_244 = l_Lean_Syntax_node1(x_219, x_243, x_242);
x_245 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_219);
x_246 = l_Lean_Syntax_node1(x_219, x_245, x_244);
x_247 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_219);
x_248 = l_Lean_Syntax_node1(x_219, x_247, x_246);
x_249 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_219);
x_250 = l_Lean_Syntax_node2(x_219, x_249, x_248, x_43);
x_251 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_252 = l_Lean_Syntax_node1(x_219, x_251, x_250);
x_253 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_252, x_7, x_8, x_9, x_10, x_238);
x_16 = x_253;
goto block_21;
}
}
case 6:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
lean_free_object(x_39);
x_254 = lean_ctor_get(x_9, 5);
lean_inc(x_254);
x_255 = l_Lean_SourceInfo_fromRef(x_254, x_38);
lean_dec(x_254);
x_256 = lean_st_ref_get(x_10, x_42);
x_257 = !lean_is_exclusive(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_258 = lean_ctor_get(x_256, 1);
x_259 = lean_ctor_get(x_256, 0);
lean_dec(x_259);
x_260 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
lean_inc(x_255);
lean_ctor_set_tag(x_256, 2);
lean_ctor_set(x_256, 1, x_260);
lean_ctor_set(x_256, 0, x_255);
x_261 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
lean_inc(x_255);
x_262 = l_Lean_Syntax_node1(x_255, x_261, x_256);
x_263 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
lean_inc(x_255);
x_264 = l_Lean_Syntax_node1(x_255, x_263, x_262);
x_265 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_255);
x_266 = l_Lean_Syntax_node1(x_255, x_265, x_264);
x_267 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_255);
x_268 = l_Lean_Syntax_node1(x_255, x_267, x_266);
x_269 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_255);
x_270 = l_Lean_Syntax_node2(x_255, x_269, x_268, x_43);
x_271 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_272 = l_Lean_Syntax_node1(x_255, x_271, x_270);
x_273 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_272, x_7, x_8, x_9, x_10, x_258);
x_16 = x_273;
goto block_21;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_274 = lean_ctor_get(x_256, 1);
lean_inc(x_274);
lean_dec(x_256);
x_275 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
lean_inc(x_255);
x_276 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_276, 0, x_255);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
lean_inc(x_255);
x_278 = l_Lean_Syntax_node1(x_255, x_277, x_276);
x_279 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
lean_inc(x_255);
x_280 = l_Lean_Syntax_node1(x_255, x_279, x_278);
x_281 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_255);
x_282 = l_Lean_Syntax_node1(x_255, x_281, x_280);
x_283 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_255);
x_284 = l_Lean_Syntax_node1(x_255, x_283, x_282);
x_285 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_255);
x_286 = l_Lean_Syntax_node2(x_255, x_285, x_284, x_43);
x_287 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_288 = l_Lean_Syntax_node1(x_255, x_287, x_286);
x_289 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_288, x_7, x_8, x_9, x_10, x_274);
x_16 = x_289;
goto block_21;
}
}
case 7:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_free_object(x_39);
x_290 = lean_ctor_get(x_9, 5);
lean_inc(x_290);
x_291 = l_Lean_SourceInfo_fromRef(x_290, x_38);
lean_dec(x_290);
x_292 = lean_st_ref_get(x_10, x_42);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_294 = lean_ctor_get(x_292, 1);
x_295 = lean_ctor_get(x_292, 0);
lean_dec(x_295);
x_296 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
lean_inc(x_291);
lean_ctor_set_tag(x_292, 2);
lean_ctor_set(x_292, 1, x_296);
lean_ctor_set(x_292, 0, x_291);
x_297 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_inc(x_291);
x_298 = l_Lean_Syntax_node1(x_291, x_297, x_292);
x_299 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
lean_inc(x_291);
x_300 = l_Lean_Syntax_node1(x_291, x_299, x_298);
x_301 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_291);
x_302 = l_Lean_Syntax_node1(x_291, x_301, x_300);
x_303 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_291);
x_304 = l_Lean_Syntax_node1(x_291, x_303, x_302);
x_305 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_291);
x_306 = l_Lean_Syntax_node2(x_291, x_305, x_304, x_43);
x_307 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_308 = l_Lean_Syntax_node1(x_291, x_307, x_306);
x_309 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_308, x_7, x_8, x_9, x_10, x_294);
x_16 = x_309;
goto block_21;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_310 = lean_ctor_get(x_292, 1);
lean_inc(x_310);
lean_dec(x_292);
x_311 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
lean_inc(x_291);
x_312 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_312, 0, x_291);
lean_ctor_set(x_312, 1, x_311);
x_313 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_inc(x_291);
x_314 = l_Lean_Syntax_node1(x_291, x_313, x_312);
x_315 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
lean_inc(x_291);
x_316 = l_Lean_Syntax_node1(x_291, x_315, x_314);
x_317 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_291);
x_318 = l_Lean_Syntax_node1(x_291, x_317, x_316);
x_319 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_291);
x_320 = l_Lean_Syntax_node1(x_291, x_319, x_318);
x_321 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_291);
x_322 = l_Lean_Syntax_node2(x_291, x_321, x_320, x_43);
x_323 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_324 = l_Lean_Syntax_node1(x_291, x_323, x_322);
x_325 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_324, x_7, x_8, x_9, x_10, x_310);
x_16 = x_325;
goto block_21;
}
}
case 8:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_free_object(x_39);
x_326 = lean_ctor_get(x_9, 5);
lean_inc(x_326);
x_327 = l_Lean_SourceInfo_fromRef(x_326, x_38);
lean_dec(x_326);
x_328 = lean_st_ref_get(x_10, x_42);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_331 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_327);
x_332 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_332, 0, x_327);
lean_ctor_set(x_332, 1, x_330);
lean_ctor_set(x_332, 2, x_331);
x_333 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_327);
x_334 = l_Lean_Syntax_node2(x_327, x_333, x_332, x_43);
x_335 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_336 = l_Lean_Syntax_node1(x_327, x_335, x_334);
x_337 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_336, x_7, x_8, x_9, x_10, x_329);
x_16 = x_337;
goto block_21;
}
default: 
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
lean_free_object(x_39);
x_338 = lean_ctor_get(x_9, 5);
lean_inc(x_338);
x_339 = l_Lean_SourceInfo_fromRef(x_338, x_38);
lean_dec(x_338);
x_340 = lean_st_ref_get(x_10, x_42);
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_342 = lean_ctor_get(x_340, 1);
x_343 = lean_ctor_get(x_340, 0);
lean_dec(x_343);
x_344 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
lean_inc(x_339);
lean_ctor_set_tag(x_340, 2);
lean_ctor_set(x_340, 1, x_344);
lean_ctor_set(x_340, 0, x_339);
x_345 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
lean_inc(x_339);
x_346 = l_Lean_Syntax_node1(x_339, x_345, x_340);
x_347 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_339);
x_348 = l_Lean_Syntax_node1(x_339, x_347, x_346);
x_349 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_339);
x_350 = l_Lean_Syntax_node1(x_339, x_349, x_348);
x_351 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_339);
x_352 = l_Lean_Syntax_node2(x_339, x_351, x_350, x_43);
x_353 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_354 = l_Lean_Syntax_node1(x_339, x_353, x_352);
x_355 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_354, x_7, x_8, x_9, x_10, x_342);
x_16 = x_355;
goto block_21;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_356 = lean_ctor_get(x_340, 1);
lean_inc(x_356);
lean_dec(x_340);
x_357 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
lean_inc(x_339);
x_358 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_358, 0, x_339);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
lean_inc(x_339);
x_360 = l_Lean_Syntax_node1(x_339, x_359, x_358);
x_361 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_339);
x_362 = l_Lean_Syntax_node1(x_339, x_361, x_360);
x_363 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_339);
x_364 = l_Lean_Syntax_node1(x_339, x_363, x_362);
x_365 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_339);
x_366 = l_Lean_Syntax_node2(x_339, x_365, x_364, x_43);
x_367 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_368 = l_Lean_Syntax_node1(x_339, x_367, x_366);
x_369 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_368, x_7, x_8, x_9, x_10, x_356);
x_16 = x_369;
goto block_21;
}
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_39, 0);
x_371 = lean_ctor_get(x_39, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_39);
x_372 = lean_mk_syntax_ident(x_370);
switch (x_23) {
case 0:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_373 = lean_ctor_get(x_9, 5);
lean_inc(x_373);
x_374 = l_Lean_SourceInfo_fromRef(x_373, x_38);
lean_dec(x_373);
x_375 = lean_st_ref_get(x_10, x_371);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_377 = x_375;
} else {
 lean_dec_ref(x_375);
 x_377 = lean_box(0);
}
x_378 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_374);
if (lean_is_scalar(x_377)) {
 x_379 = lean_alloc_ctor(2, 2, 0);
} else {
 x_379 = x_377;
 lean_ctor_set_tag(x_379, 2);
}
lean_ctor_set(x_379, 0, x_374);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
lean_inc(x_374);
x_381 = l_Lean_Syntax_node1(x_374, x_380, x_379);
x_382 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_374);
x_383 = l_Lean_Syntax_node1(x_374, x_382, x_381);
x_384 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_374);
x_385 = l_Lean_Syntax_node1(x_374, x_384, x_383);
x_386 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_374);
x_387 = l_Lean_Syntax_node2(x_374, x_386, x_385, x_372);
x_388 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_389 = l_Lean_Syntax_node1(x_374, x_388, x_387);
x_390 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_389, x_7, x_8, x_9, x_10, x_376);
x_16 = x_390;
goto block_21;
}
case 1:
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_391 = lean_ctor_get(x_9, 5);
lean_inc(x_391);
x_392 = l_Lean_SourceInfo_fromRef(x_391, x_38);
lean_dec(x_391);
x_393 = lean_st_ref_get(x_10, x_371);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_395 = x_393;
} else {
 lean_dec_ref(x_393);
 x_395 = lean_box(0);
}
x_396 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_392);
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(2, 2, 0);
} else {
 x_397 = x_395;
 lean_ctor_set_tag(x_397, 2);
}
lean_ctor_set(x_397, 0, x_392);
lean_ctor_set(x_397, 1, x_396);
x_398 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_392);
x_399 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_399, 0, x_392);
lean_ctor_set(x_399, 1, x_398);
x_400 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
lean_inc(x_392);
x_401 = l_Lean_Syntax_node2(x_392, x_400, x_397, x_399);
x_402 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_392);
x_403 = l_Lean_Syntax_node1(x_392, x_402, x_401);
x_404 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_392);
x_405 = l_Lean_Syntax_node1(x_392, x_404, x_403);
x_406 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_392);
x_407 = l_Lean_Syntax_node2(x_392, x_406, x_405, x_372);
x_408 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_409 = l_Lean_Syntax_node1(x_392, x_408, x_407);
x_410 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_409, x_7, x_8, x_9, x_10, x_394);
x_16 = x_410;
goto block_21;
}
case 2:
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_411 = lean_ctor_get(x_9, 5);
lean_inc(x_411);
x_412 = l_Lean_SourceInfo_fromRef(x_411, x_38);
lean_dec(x_411);
x_413 = lean_st_ref_get(x_10, x_371);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_415 = x_413;
} else {
 lean_dec_ref(x_413);
 x_415 = lean_box(0);
}
x_416 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_412);
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(2, 2, 0);
} else {
 x_417 = x_415;
 lean_ctor_set_tag(x_417, 2);
}
lean_ctor_set(x_417, 0, x_412);
lean_ctor_set(x_417, 1, x_416);
x_418 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_412);
x_419 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_419, 0, x_412);
lean_ctor_set(x_419, 1, x_418);
x_420 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_inc(x_417);
lean_inc(x_412);
x_421 = l_Lean_Syntax_node3(x_412, x_420, x_417, x_419, x_417);
x_422 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_412);
x_423 = l_Lean_Syntax_node1(x_412, x_422, x_421);
x_424 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_412);
x_425 = l_Lean_Syntax_node1(x_412, x_424, x_423);
x_426 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_412);
x_427 = l_Lean_Syntax_node2(x_412, x_426, x_425, x_372);
x_428 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_429 = l_Lean_Syntax_node1(x_412, x_428, x_427);
x_430 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_429, x_7, x_8, x_9, x_10, x_414);
x_16 = x_430;
goto block_21;
}
case 3:
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_431 = lean_ctor_get(x_9, 5);
lean_inc(x_431);
x_432 = l_Lean_SourceInfo_fromRef(x_431, x_38);
lean_dec(x_431);
x_433 = lean_st_ref_get(x_10, x_371);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_435 = x_433;
} else {
 lean_dec_ref(x_433);
 x_435 = lean_box(0);
}
x_436 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_432);
if (lean_is_scalar(x_435)) {
 x_437 = lean_alloc_ctor(2, 2, 0);
} else {
 x_437 = x_435;
 lean_ctor_set_tag(x_437, 2);
}
lean_ctor_set(x_437, 0, x_432);
lean_ctor_set(x_437, 1, x_436);
x_438 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_432);
x_439 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_439, 0, x_432);
lean_ctor_set(x_439, 1, x_438);
x_440 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
lean_inc(x_432);
x_441 = l_Lean_Syntax_node2(x_432, x_440, x_437, x_439);
x_442 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
lean_inc(x_432);
x_443 = l_Lean_Syntax_node1(x_432, x_442, x_441);
x_444 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_432);
x_445 = l_Lean_Syntax_node1(x_432, x_444, x_443);
x_446 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_432);
x_447 = l_Lean_Syntax_node1(x_432, x_446, x_445);
x_448 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_432);
x_449 = l_Lean_Syntax_node2(x_432, x_448, x_447, x_372);
x_450 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_451 = l_Lean_Syntax_node1(x_432, x_450, x_449);
x_452 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_451, x_7, x_8, x_9, x_10, x_434);
x_16 = x_452;
goto block_21;
}
case 4:
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_453 = lean_ctor_get(x_9, 5);
lean_inc(x_453);
x_454 = l_Lean_SourceInfo_fromRef(x_453, x_38);
lean_dec(x_453);
x_455 = lean_st_ref_get(x_10, x_371);
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_457 = x_455;
} else {
 lean_dec_ref(x_455);
 x_457 = lean_box(0);
}
x_458 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
lean_inc(x_454);
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(2, 2, 0);
} else {
 x_459 = x_457;
 lean_ctor_set_tag(x_459, 2);
}
lean_ctor_set(x_459, 0, x_454);
lean_ctor_set(x_459, 1, x_458);
x_460 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_inc(x_454);
x_461 = l_Lean_Syntax_node1(x_454, x_460, x_459);
x_462 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_inc(x_454);
x_463 = l_Lean_Syntax_node1(x_454, x_462, x_461);
x_464 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_454);
x_465 = l_Lean_Syntax_node1(x_454, x_464, x_463);
x_466 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_454);
x_467 = l_Lean_Syntax_node1(x_454, x_466, x_465);
x_468 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_454);
x_469 = l_Lean_Syntax_node2(x_454, x_468, x_467, x_372);
x_470 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_471 = l_Lean_Syntax_node1(x_454, x_470, x_469);
x_472 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_471, x_7, x_8, x_9, x_10, x_456);
x_16 = x_472;
goto block_21;
}
case 5:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_473 = lean_ctor_get(x_9, 5);
lean_inc(x_473);
x_474 = l_Lean_SourceInfo_fromRef(x_473, x_38);
lean_dec(x_473);
x_475 = lean_st_ref_get(x_10, x_371);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
x_478 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_474);
if (lean_is_scalar(x_477)) {
 x_479 = lean_alloc_ctor(2, 2, 0);
} else {
 x_479 = x_477;
 lean_ctor_set_tag(x_479, 2);
}
lean_ctor_set(x_479, 0, x_474);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
lean_inc(x_474);
x_481 = l_Lean_Syntax_node1(x_474, x_480, x_479);
x_482 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
lean_inc(x_474);
x_483 = l_Lean_Syntax_node1(x_474, x_482, x_481);
x_484 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_474);
x_485 = l_Lean_Syntax_node1(x_474, x_484, x_483);
x_486 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_474);
x_487 = l_Lean_Syntax_node1(x_474, x_486, x_485);
x_488 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_474);
x_489 = l_Lean_Syntax_node2(x_474, x_488, x_487, x_372);
x_490 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_491 = l_Lean_Syntax_node1(x_474, x_490, x_489);
x_492 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_491, x_7, x_8, x_9, x_10, x_476);
x_16 = x_492;
goto block_21;
}
case 6:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_493 = lean_ctor_get(x_9, 5);
lean_inc(x_493);
x_494 = l_Lean_SourceInfo_fromRef(x_493, x_38);
lean_dec(x_493);
x_495 = lean_st_ref_get(x_10, x_371);
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_497 = x_495;
} else {
 lean_dec_ref(x_495);
 x_497 = lean_box(0);
}
x_498 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
lean_inc(x_494);
if (lean_is_scalar(x_497)) {
 x_499 = lean_alloc_ctor(2, 2, 0);
} else {
 x_499 = x_497;
 lean_ctor_set_tag(x_499, 2);
}
lean_ctor_set(x_499, 0, x_494);
lean_ctor_set(x_499, 1, x_498);
x_500 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
lean_inc(x_494);
x_501 = l_Lean_Syntax_node1(x_494, x_500, x_499);
x_502 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
lean_inc(x_494);
x_503 = l_Lean_Syntax_node1(x_494, x_502, x_501);
x_504 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_494);
x_505 = l_Lean_Syntax_node1(x_494, x_504, x_503);
x_506 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_494);
x_507 = l_Lean_Syntax_node1(x_494, x_506, x_505);
x_508 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_494);
x_509 = l_Lean_Syntax_node2(x_494, x_508, x_507, x_372);
x_510 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_511 = l_Lean_Syntax_node1(x_494, x_510, x_509);
x_512 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_511, x_7, x_8, x_9, x_10, x_496);
x_16 = x_512;
goto block_21;
}
case 7:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_513 = lean_ctor_get(x_9, 5);
lean_inc(x_513);
x_514 = l_Lean_SourceInfo_fromRef(x_513, x_38);
lean_dec(x_513);
x_515 = lean_st_ref_get(x_10, x_371);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_517 = x_515;
} else {
 lean_dec_ref(x_515);
 x_517 = lean_box(0);
}
x_518 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
lean_inc(x_514);
if (lean_is_scalar(x_517)) {
 x_519 = lean_alloc_ctor(2, 2, 0);
} else {
 x_519 = x_517;
 lean_ctor_set_tag(x_519, 2);
}
lean_ctor_set(x_519, 0, x_514);
lean_ctor_set(x_519, 1, x_518);
x_520 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_inc(x_514);
x_521 = l_Lean_Syntax_node1(x_514, x_520, x_519);
x_522 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
lean_inc(x_514);
x_523 = l_Lean_Syntax_node1(x_514, x_522, x_521);
x_524 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_514);
x_525 = l_Lean_Syntax_node1(x_514, x_524, x_523);
x_526 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_514);
x_527 = l_Lean_Syntax_node1(x_514, x_526, x_525);
x_528 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_514);
x_529 = l_Lean_Syntax_node2(x_514, x_528, x_527, x_372);
x_530 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_531 = l_Lean_Syntax_node1(x_514, x_530, x_529);
x_532 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_531, x_7, x_8, x_9, x_10, x_516);
x_16 = x_532;
goto block_21;
}
case 8:
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_533 = lean_ctor_get(x_9, 5);
lean_inc(x_533);
x_534 = l_Lean_SourceInfo_fromRef(x_533, x_38);
lean_dec(x_533);
x_535 = lean_st_ref_get(x_10, x_371);
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_537 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_538 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_534);
x_539 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_539, 0, x_534);
lean_ctor_set(x_539, 1, x_537);
lean_ctor_set(x_539, 2, x_538);
x_540 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_534);
x_541 = l_Lean_Syntax_node2(x_534, x_540, x_539, x_372);
x_542 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_543 = l_Lean_Syntax_node1(x_534, x_542, x_541);
x_544 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_543, x_7, x_8, x_9, x_10, x_536);
x_16 = x_544;
goto block_21;
}
default: 
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_545 = lean_ctor_get(x_9, 5);
lean_inc(x_545);
x_546 = l_Lean_SourceInfo_fromRef(x_545, x_38);
lean_dec(x_545);
x_547 = lean_st_ref_get(x_10, x_371);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_549 = x_547;
} else {
 lean_dec_ref(x_547);
 x_549 = lean_box(0);
}
x_550 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
lean_inc(x_546);
if (lean_is_scalar(x_549)) {
 x_551 = lean_alloc_ctor(2, 2, 0);
} else {
 x_551 = x_549;
 lean_ctor_set_tag(x_551, 2);
}
lean_ctor_set(x_551, 0, x_546);
lean_ctor_set(x_551, 1, x_550);
x_552 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
lean_inc(x_546);
x_553 = l_Lean_Syntax_node1(x_546, x_552, x_551);
x_554 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_546);
x_555 = l_Lean_Syntax_node1(x_546, x_554, x_553);
x_556 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_546);
x_557 = l_Lean_Syntax_node1(x_546, x_556, x_555);
x_558 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_546);
x_559 = l_Lean_Syntax_node2(x_546, x_558, x_557, x_372);
x_560 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_561 = l_Lean_Syntax_node1(x_546, x_560, x_559);
x_562 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_561, x_7, x_8, x_9, x_10, x_548);
x_16 = x_562;
goto block_21;
}
}
}
}
else
{
uint8_t x_563; 
lean_dec(x_28);
x_563 = !lean_is_exclusive(x_35);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; uint8_t x_566; 
x_564 = lean_ctor_get(x_35, 1);
x_565 = lean_ctor_get(x_35, 0);
lean_dec(x_565);
x_566 = !lean_is_exclusive(x_36);
if (x_566 == 0)
{
lean_object* x_567; uint8_t x_568; 
x_567 = lean_ctor_get(x_36, 0);
x_568 = l_Lean_NameSet_contains(x_26, x_567);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
lean_free_object(x_35);
x_569 = lean_box(0);
lean_inc(x_567);
x_570 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_26, x_567, x_569);
x_571 = 0;
lean_inc(x_9);
x_572 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_567, x_571, x_7, x_8, x_9, x_10, x_564);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_575 = lean_mk_syntax_ident(x_573);
x_576 = lean_ctor_get(x_9, 5);
lean_inc(x_576);
x_577 = l_Lean_SourceInfo_fromRef(x_576, x_571);
lean_dec(x_576);
x_578 = lean_st_ref_get(x_10, x_574);
x_579 = !lean_is_exclusive(x_578);
if (x_579 == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_580 = lean_ctor_get(x_578, 0);
lean_dec(x_580);
x_581 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_582 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_577);
x_583 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_583, 0, x_577);
lean_ctor_set(x_583, 1, x_581);
lean_ctor_set(x_583, 2, x_582);
x_584 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_577);
x_585 = l_Lean_Syntax_node2(x_577, x_584, x_583, x_575);
x_586 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_587 = l_Lean_Syntax_node1(x_577, x_586, x_585);
x_588 = lean_array_push(x_27, x_587);
lean_ctor_set(x_5, 1, x_588);
lean_ctor_set(x_5, 0, x_570);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_578, 0, x_36);
x_16 = x_578;
goto block_21;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_589 = lean_ctor_get(x_578, 1);
lean_inc(x_589);
lean_dec(x_578);
x_590 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_591 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_577);
x_592 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_592, 0, x_577);
lean_ctor_set(x_592, 1, x_590);
lean_ctor_set(x_592, 2, x_591);
x_593 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_577);
x_594 = l_Lean_Syntax_node2(x_577, x_593, x_592, x_575);
x_595 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_596 = l_Lean_Syntax_node1(x_577, x_595, x_594);
x_597 = lean_array_push(x_27, x_596);
lean_ctor_set(x_5, 1, x_597);
lean_ctor_set(x_5, 0, x_570);
lean_ctor_set(x_36, 0, x_5);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_36);
lean_ctor_set(x_598, 1, x_589);
x_16 = x_598;
goto block_21;
}
}
else
{
lean_dec(x_567);
lean_ctor_set(x_36, 0, x_5);
x_16 = x_35;
goto block_21;
}
}
else
{
lean_object* x_599; uint8_t x_600; 
x_599 = lean_ctor_get(x_36, 0);
lean_inc(x_599);
lean_dec(x_36);
x_600 = l_Lean_NameSet_contains(x_26, x_599);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_free_object(x_35);
x_601 = lean_box(0);
lean_inc(x_599);
x_602 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_26, x_599, x_601);
x_603 = 0;
lean_inc(x_9);
x_604 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_599, x_603, x_7, x_8, x_9, x_10, x_564);
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec(x_604);
x_607 = lean_mk_syntax_ident(x_605);
x_608 = lean_ctor_get(x_9, 5);
lean_inc(x_608);
x_609 = l_Lean_SourceInfo_fromRef(x_608, x_603);
lean_dec(x_608);
x_610 = lean_st_ref_get(x_10, x_606);
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_612 = x_610;
} else {
 lean_dec_ref(x_610);
 x_612 = lean_box(0);
}
x_613 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_614 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_609);
x_615 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_615, 0, x_609);
lean_ctor_set(x_615, 1, x_613);
lean_ctor_set(x_615, 2, x_614);
x_616 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_609);
x_617 = l_Lean_Syntax_node2(x_609, x_616, x_615, x_607);
x_618 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_619 = l_Lean_Syntax_node1(x_609, x_618, x_617);
x_620 = lean_array_push(x_27, x_619);
lean_ctor_set(x_5, 1, x_620);
lean_ctor_set(x_5, 0, x_602);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_5);
if (lean_is_scalar(x_612)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_612;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_611);
x_16 = x_622;
goto block_21;
}
else
{
lean_object* x_623; 
lean_dec(x_599);
x_623 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_623, 0, x_5);
lean_ctor_set(x_35, 0, x_623);
x_16 = x_35;
goto block_21;
}
}
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
x_624 = lean_ctor_get(x_35, 1);
lean_inc(x_624);
lean_dec(x_35);
x_625 = lean_ctor_get(x_36, 0);
lean_inc(x_625);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_626 = x_36;
} else {
 lean_dec_ref(x_36);
 x_626 = lean_box(0);
}
x_627 = l_Lean_NameSet_contains(x_26, x_625);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; uint8_t x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_628 = lean_box(0);
lean_inc(x_625);
x_629 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_26, x_625, x_628);
x_630 = 0;
lean_inc(x_9);
x_631 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_625, x_630, x_7, x_8, x_9, x_10, x_624);
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = lean_mk_syntax_ident(x_632);
x_635 = lean_ctor_get(x_9, 5);
lean_inc(x_635);
x_636 = l_Lean_SourceInfo_fromRef(x_635, x_630);
lean_dec(x_635);
x_637 = lean_st_ref_get(x_10, x_633);
x_638 = lean_ctor_get(x_637, 1);
lean_inc(x_638);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_639 = x_637;
} else {
 lean_dec_ref(x_637);
 x_639 = lean_box(0);
}
x_640 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_641 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_636);
x_642 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_642, 0, x_636);
lean_ctor_set(x_642, 1, x_640);
lean_ctor_set(x_642, 2, x_641);
x_643 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_636);
x_644 = l_Lean_Syntax_node2(x_636, x_643, x_642, x_634);
x_645 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_646 = l_Lean_Syntax_node1(x_636, x_645, x_644);
x_647 = lean_array_push(x_27, x_646);
lean_ctor_set(x_5, 1, x_647);
lean_ctor_set(x_5, 0, x_629);
if (lean_is_scalar(x_626)) {
 x_648 = lean_alloc_ctor(1, 1, 0);
} else {
 x_648 = x_626;
}
lean_ctor_set(x_648, 0, x_5);
if (lean_is_scalar(x_639)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_639;
}
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_638);
x_16 = x_649;
goto block_21;
}
else
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_625);
if (lean_is_scalar(x_626)) {
 x_650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_650 = x_626;
}
lean_ctor_set(x_650, 0, x_5);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_624);
x_16 = x_651;
goto block_21;
}
}
}
}
else
{
lean_dec(x_28);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_29, 0, x_22);
x_16 = x_29;
goto block_21;
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_652 = lean_ctor_get(x_29, 0);
x_653 = lean_ctor_get(x_29, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_29);
x_654 = lean_ctor_get(x_652, 0);
lean_inc(x_654);
lean_dec(x_652);
x_655 = l_Lean_Meta_Match_isMatchEqnTheorem(x_654, x_28);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; 
lean_free_object(x_22);
x_656 = l_Lean_Meta_isEqnThm_x3f(x_28, x_9, x_10, x_653);
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; uint8_t x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_free_object(x_5);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
x_659 = 0;
lean_inc(x_9);
x_660 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_28, x_659, x_7, x_8, x_9, x_10, x_658);
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_663 = x_660;
} else {
 lean_dec_ref(x_660);
 x_663 = lean_box(0);
}
x_664 = lean_mk_syntax_ident(x_661);
switch (x_23) {
case 0:
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_663);
x_665 = lean_ctor_get(x_9, 5);
lean_inc(x_665);
x_666 = l_Lean_SourceInfo_fromRef(x_665, x_659);
lean_dec(x_665);
x_667 = lean_st_ref_get(x_10, x_662);
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_669 = x_667;
} else {
 lean_dec_ref(x_667);
 x_669 = lean_box(0);
}
x_670 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_666);
if (lean_is_scalar(x_669)) {
 x_671 = lean_alloc_ctor(2, 2, 0);
} else {
 x_671 = x_669;
 lean_ctor_set_tag(x_671, 2);
}
lean_ctor_set(x_671, 0, x_666);
lean_ctor_set(x_671, 1, x_670);
x_672 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
lean_inc(x_666);
x_673 = l_Lean_Syntax_node1(x_666, x_672, x_671);
x_674 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_666);
x_675 = l_Lean_Syntax_node1(x_666, x_674, x_673);
x_676 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_666);
x_677 = l_Lean_Syntax_node1(x_666, x_676, x_675);
x_678 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_666);
x_679 = l_Lean_Syntax_node2(x_666, x_678, x_677, x_664);
x_680 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_681 = l_Lean_Syntax_node1(x_666, x_680, x_679);
x_682 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_681, x_7, x_8, x_9, x_10, x_668);
x_16 = x_682;
goto block_21;
}
case 1:
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
x_683 = lean_ctor_get(x_9, 5);
lean_inc(x_683);
x_684 = l_Lean_SourceInfo_fromRef(x_683, x_659);
lean_dec(x_683);
x_685 = lean_st_ref_get(x_10, x_662);
x_686 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_687 = x_685;
} else {
 lean_dec_ref(x_685);
 x_687 = lean_box(0);
}
x_688 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_684);
if (lean_is_scalar(x_687)) {
 x_689 = lean_alloc_ctor(2, 2, 0);
} else {
 x_689 = x_687;
 lean_ctor_set_tag(x_689, 2);
}
lean_ctor_set(x_689, 0, x_684);
lean_ctor_set(x_689, 1, x_688);
x_690 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_684);
if (lean_is_scalar(x_663)) {
 x_691 = lean_alloc_ctor(2, 2, 0);
} else {
 x_691 = x_663;
 lean_ctor_set_tag(x_691, 2);
}
lean_ctor_set(x_691, 0, x_684);
lean_ctor_set(x_691, 1, x_690);
x_692 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
lean_inc(x_684);
x_693 = l_Lean_Syntax_node2(x_684, x_692, x_689, x_691);
x_694 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_684);
x_695 = l_Lean_Syntax_node1(x_684, x_694, x_693);
x_696 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_684);
x_697 = l_Lean_Syntax_node1(x_684, x_696, x_695);
x_698 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_684);
x_699 = l_Lean_Syntax_node2(x_684, x_698, x_697, x_664);
x_700 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_701 = l_Lean_Syntax_node1(x_684, x_700, x_699);
x_702 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_701, x_7, x_8, x_9, x_10, x_686);
x_16 = x_702;
goto block_21;
}
case 2:
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_703 = lean_ctor_get(x_9, 5);
lean_inc(x_703);
x_704 = l_Lean_SourceInfo_fromRef(x_703, x_659);
lean_dec(x_703);
x_705 = lean_st_ref_get(x_10, x_662);
x_706 = lean_ctor_get(x_705, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_705)) {
 lean_ctor_release(x_705, 0);
 lean_ctor_release(x_705, 1);
 x_707 = x_705;
} else {
 lean_dec_ref(x_705);
 x_707 = lean_box(0);
}
x_708 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_704);
if (lean_is_scalar(x_707)) {
 x_709 = lean_alloc_ctor(2, 2, 0);
} else {
 x_709 = x_707;
 lean_ctor_set_tag(x_709, 2);
}
lean_ctor_set(x_709, 0, x_704);
lean_ctor_set(x_709, 1, x_708);
x_710 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_704);
if (lean_is_scalar(x_663)) {
 x_711 = lean_alloc_ctor(2, 2, 0);
} else {
 x_711 = x_663;
 lean_ctor_set_tag(x_711, 2);
}
lean_ctor_set(x_711, 0, x_704);
lean_ctor_set(x_711, 1, x_710);
x_712 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_inc(x_709);
lean_inc(x_704);
x_713 = l_Lean_Syntax_node3(x_704, x_712, x_709, x_711, x_709);
x_714 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_704);
x_715 = l_Lean_Syntax_node1(x_704, x_714, x_713);
x_716 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_704);
x_717 = l_Lean_Syntax_node1(x_704, x_716, x_715);
x_718 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_704);
x_719 = l_Lean_Syntax_node2(x_704, x_718, x_717, x_664);
x_720 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_721 = l_Lean_Syntax_node1(x_704, x_720, x_719);
x_722 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_721, x_7, x_8, x_9, x_10, x_706);
x_16 = x_722;
goto block_21;
}
case 3:
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_723 = lean_ctor_get(x_9, 5);
lean_inc(x_723);
x_724 = l_Lean_SourceInfo_fromRef(x_723, x_659);
lean_dec(x_723);
x_725 = lean_st_ref_get(x_10, x_662);
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_727 = x_725;
} else {
 lean_dec_ref(x_725);
 x_727 = lean_box(0);
}
x_728 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_724);
if (lean_is_scalar(x_727)) {
 x_729 = lean_alloc_ctor(2, 2, 0);
} else {
 x_729 = x_727;
 lean_ctor_set_tag(x_729, 2);
}
lean_ctor_set(x_729, 0, x_724);
lean_ctor_set(x_729, 1, x_728);
x_730 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_724);
if (lean_is_scalar(x_663)) {
 x_731 = lean_alloc_ctor(2, 2, 0);
} else {
 x_731 = x_663;
 lean_ctor_set_tag(x_731, 2);
}
lean_ctor_set(x_731, 0, x_724);
lean_ctor_set(x_731, 1, x_730);
x_732 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
lean_inc(x_724);
x_733 = l_Lean_Syntax_node2(x_724, x_732, x_729, x_731);
x_734 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
lean_inc(x_724);
x_735 = l_Lean_Syntax_node1(x_724, x_734, x_733);
x_736 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_724);
x_737 = l_Lean_Syntax_node1(x_724, x_736, x_735);
x_738 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_724);
x_739 = l_Lean_Syntax_node1(x_724, x_738, x_737);
x_740 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_724);
x_741 = l_Lean_Syntax_node2(x_724, x_740, x_739, x_664);
x_742 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_743 = l_Lean_Syntax_node1(x_724, x_742, x_741);
x_744 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_743, x_7, x_8, x_9, x_10, x_726);
x_16 = x_744;
goto block_21;
}
case 4:
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_663);
x_745 = lean_ctor_get(x_9, 5);
lean_inc(x_745);
x_746 = l_Lean_SourceInfo_fromRef(x_745, x_659);
lean_dec(x_745);
x_747 = lean_st_ref_get(x_10, x_662);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_749 = x_747;
} else {
 lean_dec_ref(x_747);
 x_749 = lean_box(0);
}
x_750 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
lean_inc(x_746);
if (lean_is_scalar(x_749)) {
 x_751 = lean_alloc_ctor(2, 2, 0);
} else {
 x_751 = x_749;
 lean_ctor_set_tag(x_751, 2);
}
lean_ctor_set(x_751, 0, x_746);
lean_ctor_set(x_751, 1, x_750);
x_752 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_inc(x_746);
x_753 = l_Lean_Syntax_node1(x_746, x_752, x_751);
x_754 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_inc(x_746);
x_755 = l_Lean_Syntax_node1(x_746, x_754, x_753);
x_756 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_746);
x_757 = l_Lean_Syntax_node1(x_746, x_756, x_755);
x_758 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_746);
x_759 = l_Lean_Syntax_node1(x_746, x_758, x_757);
x_760 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_746);
x_761 = l_Lean_Syntax_node2(x_746, x_760, x_759, x_664);
x_762 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_763 = l_Lean_Syntax_node1(x_746, x_762, x_761);
x_764 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_763, x_7, x_8, x_9, x_10, x_748);
x_16 = x_764;
goto block_21;
}
case 5:
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_663);
x_765 = lean_ctor_get(x_9, 5);
lean_inc(x_765);
x_766 = l_Lean_SourceInfo_fromRef(x_765, x_659);
lean_dec(x_765);
x_767 = lean_st_ref_get(x_10, x_662);
x_768 = lean_ctor_get(x_767, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 x_769 = x_767;
} else {
 lean_dec_ref(x_767);
 x_769 = lean_box(0);
}
x_770 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_766);
if (lean_is_scalar(x_769)) {
 x_771 = lean_alloc_ctor(2, 2, 0);
} else {
 x_771 = x_769;
 lean_ctor_set_tag(x_771, 2);
}
lean_ctor_set(x_771, 0, x_766);
lean_ctor_set(x_771, 1, x_770);
x_772 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
lean_inc(x_766);
x_773 = l_Lean_Syntax_node1(x_766, x_772, x_771);
x_774 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
lean_inc(x_766);
x_775 = l_Lean_Syntax_node1(x_766, x_774, x_773);
x_776 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_766);
x_777 = l_Lean_Syntax_node1(x_766, x_776, x_775);
x_778 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_766);
x_779 = l_Lean_Syntax_node1(x_766, x_778, x_777);
x_780 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_766);
x_781 = l_Lean_Syntax_node2(x_766, x_780, x_779, x_664);
x_782 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_783 = l_Lean_Syntax_node1(x_766, x_782, x_781);
x_784 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_783, x_7, x_8, x_9, x_10, x_768);
x_16 = x_784;
goto block_21;
}
case 6:
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec(x_663);
x_785 = lean_ctor_get(x_9, 5);
lean_inc(x_785);
x_786 = l_Lean_SourceInfo_fromRef(x_785, x_659);
lean_dec(x_785);
x_787 = lean_st_ref_get(x_10, x_662);
x_788 = lean_ctor_get(x_787, 1);
lean_inc(x_788);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_789 = x_787;
} else {
 lean_dec_ref(x_787);
 x_789 = lean_box(0);
}
x_790 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
lean_inc(x_786);
if (lean_is_scalar(x_789)) {
 x_791 = lean_alloc_ctor(2, 2, 0);
} else {
 x_791 = x_789;
 lean_ctor_set_tag(x_791, 2);
}
lean_ctor_set(x_791, 0, x_786);
lean_ctor_set(x_791, 1, x_790);
x_792 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
lean_inc(x_786);
x_793 = l_Lean_Syntax_node1(x_786, x_792, x_791);
x_794 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
lean_inc(x_786);
x_795 = l_Lean_Syntax_node1(x_786, x_794, x_793);
x_796 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_786);
x_797 = l_Lean_Syntax_node1(x_786, x_796, x_795);
x_798 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_786);
x_799 = l_Lean_Syntax_node1(x_786, x_798, x_797);
x_800 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_786);
x_801 = l_Lean_Syntax_node2(x_786, x_800, x_799, x_664);
x_802 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_803 = l_Lean_Syntax_node1(x_786, x_802, x_801);
x_804 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_803, x_7, x_8, x_9, x_10, x_788);
x_16 = x_804;
goto block_21;
}
case 7:
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_663);
x_805 = lean_ctor_get(x_9, 5);
lean_inc(x_805);
x_806 = l_Lean_SourceInfo_fromRef(x_805, x_659);
lean_dec(x_805);
x_807 = lean_st_ref_get(x_10, x_662);
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_809 = x_807;
} else {
 lean_dec_ref(x_807);
 x_809 = lean_box(0);
}
x_810 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
lean_inc(x_806);
if (lean_is_scalar(x_809)) {
 x_811 = lean_alloc_ctor(2, 2, 0);
} else {
 x_811 = x_809;
 lean_ctor_set_tag(x_811, 2);
}
lean_ctor_set(x_811, 0, x_806);
lean_ctor_set(x_811, 1, x_810);
x_812 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_inc(x_806);
x_813 = l_Lean_Syntax_node1(x_806, x_812, x_811);
x_814 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
lean_inc(x_806);
x_815 = l_Lean_Syntax_node1(x_806, x_814, x_813);
x_816 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_806);
x_817 = l_Lean_Syntax_node1(x_806, x_816, x_815);
x_818 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_806);
x_819 = l_Lean_Syntax_node1(x_806, x_818, x_817);
x_820 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_806);
x_821 = l_Lean_Syntax_node2(x_806, x_820, x_819, x_664);
x_822 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_823 = l_Lean_Syntax_node1(x_806, x_822, x_821);
x_824 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_823, x_7, x_8, x_9, x_10, x_808);
x_16 = x_824;
goto block_21;
}
case 8:
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_663);
x_825 = lean_ctor_get(x_9, 5);
lean_inc(x_825);
x_826 = l_Lean_SourceInfo_fromRef(x_825, x_659);
lean_dec(x_825);
x_827 = lean_st_ref_get(x_10, x_662);
x_828 = lean_ctor_get(x_827, 1);
lean_inc(x_828);
lean_dec(x_827);
x_829 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_830 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_826);
x_831 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_831, 0, x_826);
lean_ctor_set(x_831, 1, x_829);
lean_ctor_set(x_831, 2, x_830);
x_832 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_826);
x_833 = l_Lean_Syntax_node2(x_826, x_832, x_831, x_664);
x_834 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_835 = l_Lean_Syntax_node1(x_826, x_834, x_833);
x_836 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_835, x_7, x_8, x_9, x_10, x_828);
x_16 = x_836;
goto block_21;
}
default: 
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_663);
x_837 = lean_ctor_get(x_9, 5);
lean_inc(x_837);
x_838 = l_Lean_SourceInfo_fromRef(x_837, x_659);
lean_dec(x_837);
x_839 = lean_st_ref_get(x_10, x_662);
x_840 = lean_ctor_get(x_839, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_841 = x_839;
} else {
 lean_dec_ref(x_839);
 x_841 = lean_box(0);
}
x_842 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
lean_inc(x_838);
if (lean_is_scalar(x_841)) {
 x_843 = lean_alloc_ctor(2, 2, 0);
} else {
 x_843 = x_841;
 lean_ctor_set_tag(x_843, 2);
}
lean_ctor_set(x_843, 0, x_838);
lean_ctor_set(x_843, 1, x_842);
x_844 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
lean_inc(x_838);
x_845 = l_Lean_Syntax_node1(x_838, x_844, x_843);
x_846 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_838);
x_847 = l_Lean_Syntax_node1(x_838, x_846, x_845);
x_848 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_838);
x_849 = l_Lean_Syntax_node1(x_838, x_848, x_847);
x_850 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_838);
x_851 = l_Lean_Syntax_node2(x_838, x_850, x_849, x_664);
x_852 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_853 = l_Lean_Syntax_node1(x_838, x_852, x_851);
x_854 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_26, x_27, x_853, x_7, x_8, x_9, x_10, x_840);
x_16 = x_854;
goto block_21;
}
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; uint8_t x_859; 
lean_dec(x_28);
x_855 = lean_ctor_get(x_656, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_856 = x_656;
} else {
 lean_dec_ref(x_656);
 x_856 = lean_box(0);
}
x_857 = lean_ctor_get(x_657, 0);
lean_inc(x_857);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 x_858 = x_657;
} else {
 lean_dec_ref(x_657);
 x_858 = lean_box(0);
}
x_859 = l_Lean_NameSet_contains(x_26, x_857);
if (x_859 == 0)
{
lean_object* x_860; lean_object* x_861; uint8_t x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; 
lean_dec(x_856);
x_860 = lean_box(0);
lean_inc(x_857);
x_861 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_26, x_857, x_860);
x_862 = 0;
lean_inc(x_9);
x_863 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_857, x_862, x_7, x_8, x_9, x_10, x_855);
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_863, 1);
lean_inc(x_865);
lean_dec(x_863);
x_866 = lean_mk_syntax_ident(x_864);
x_867 = lean_ctor_get(x_9, 5);
lean_inc(x_867);
x_868 = l_Lean_SourceInfo_fromRef(x_867, x_862);
lean_dec(x_867);
x_869 = lean_st_ref_get(x_10, x_865);
x_870 = lean_ctor_get(x_869, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_871 = x_869;
} else {
 lean_dec_ref(x_869);
 x_871 = lean_box(0);
}
x_872 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_873 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_868);
x_874 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_874, 0, x_868);
lean_ctor_set(x_874, 1, x_872);
lean_ctor_set(x_874, 2, x_873);
x_875 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_868);
x_876 = l_Lean_Syntax_node2(x_868, x_875, x_874, x_866);
x_877 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_878 = l_Lean_Syntax_node1(x_868, x_877, x_876);
x_879 = lean_array_push(x_27, x_878);
lean_ctor_set(x_5, 1, x_879);
lean_ctor_set(x_5, 0, x_861);
if (lean_is_scalar(x_858)) {
 x_880 = lean_alloc_ctor(1, 1, 0);
} else {
 x_880 = x_858;
}
lean_ctor_set(x_880, 0, x_5);
if (lean_is_scalar(x_871)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_871;
}
lean_ctor_set(x_881, 0, x_880);
lean_ctor_set(x_881, 1, x_870);
x_16 = x_881;
goto block_21;
}
else
{
lean_object* x_882; lean_object* x_883; 
lean_dec(x_857);
if (lean_is_scalar(x_858)) {
 x_882 = lean_alloc_ctor(1, 1, 0);
} else {
 x_882 = x_858;
}
lean_ctor_set(x_882, 0, x_5);
if (lean_is_scalar(x_856)) {
 x_883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_883 = x_856;
}
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_855);
x_16 = x_883;
goto block_21;
}
}
}
else
{
lean_object* x_884; 
lean_dec(x_28);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_5);
x_884 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_884, 0, x_22);
lean_ctor_set(x_884, 1, x_653);
x_16 = x_884;
goto block_21;
}
}
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; 
x_885 = lean_ctor_get(x_5, 0);
x_886 = lean_ctor_get(x_5, 1);
x_887 = lean_ctor_get(x_22, 0);
lean_inc(x_887);
lean_dec(x_22);
x_888 = lean_st_ref_get(x_10, x_11);
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_891 = x_888;
} else {
 lean_dec_ref(x_888);
 x_891 = lean_box(0);
}
x_892 = lean_ctor_get(x_889, 0);
lean_inc(x_892);
lean_dec(x_889);
x_893 = l_Lean_Meta_Match_isMatchEqnTheorem(x_892, x_887);
if (x_893 == 0)
{
lean_object* x_894; lean_object* x_895; 
lean_dec(x_891);
x_894 = l_Lean_Meta_isEqnThm_x3f(x_887, x_9, x_10, x_890);
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
if (lean_obj_tag(x_895) == 0)
{
lean_object* x_896; uint8_t x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_free_object(x_5);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
lean_dec(x_894);
x_897 = 0;
lean_inc(x_9);
x_898 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_887, x_897, x_7, x_8, x_9, x_10, x_896);
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_901 = x_898;
} else {
 lean_dec_ref(x_898);
 x_901 = lean_box(0);
}
x_902 = lean_mk_syntax_ident(x_899);
switch (x_23) {
case 0:
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
lean_dec(x_901);
x_903 = lean_ctor_get(x_9, 5);
lean_inc(x_903);
x_904 = l_Lean_SourceInfo_fromRef(x_903, x_897);
lean_dec(x_903);
x_905 = lean_st_ref_get(x_10, x_900);
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_907 = x_905;
} else {
 lean_dec_ref(x_905);
 x_907 = lean_box(0);
}
x_908 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_904);
if (lean_is_scalar(x_907)) {
 x_909 = lean_alloc_ctor(2, 2, 0);
} else {
 x_909 = x_907;
 lean_ctor_set_tag(x_909, 2);
}
lean_ctor_set(x_909, 0, x_904);
lean_ctor_set(x_909, 1, x_908);
x_910 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
lean_inc(x_904);
x_911 = l_Lean_Syntax_node1(x_904, x_910, x_909);
x_912 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_904);
x_913 = l_Lean_Syntax_node1(x_904, x_912, x_911);
x_914 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_904);
x_915 = l_Lean_Syntax_node1(x_904, x_914, x_913);
x_916 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_904);
x_917 = l_Lean_Syntax_node2(x_904, x_916, x_915, x_902);
x_918 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_919 = l_Lean_Syntax_node1(x_904, x_918, x_917);
x_920 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_919, x_7, x_8, x_9, x_10, x_906);
x_16 = x_920;
goto block_21;
}
case 1:
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_921 = lean_ctor_get(x_9, 5);
lean_inc(x_921);
x_922 = l_Lean_SourceInfo_fromRef(x_921, x_897);
lean_dec(x_921);
x_923 = lean_st_ref_get(x_10, x_900);
x_924 = lean_ctor_get(x_923, 1);
lean_inc(x_924);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 lean_ctor_release(x_923, 1);
 x_925 = x_923;
} else {
 lean_dec_ref(x_923);
 x_925 = lean_box(0);
}
x_926 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_922);
if (lean_is_scalar(x_925)) {
 x_927 = lean_alloc_ctor(2, 2, 0);
} else {
 x_927 = x_925;
 lean_ctor_set_tag(x_927, 2);
}
lean_ctor_set(x_927, 0, x_922);
lean_ctor_set(x_927, 1, x_926);
x_928 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_922);
if (lean_is_scalar(x_901)) {
 x_929 = lean_alloc_ctor(2, 2, 0);
} else {
 x_929 = x_901;
 lean_ctor_set_tag(x_929, 2);
}
lean_ctor_set(x_929, 0, x_922);
lean_ctor_set(x_929, 1, x_928);
x_930 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
lean_inc(x_922);
x_931 = l_Lean_Syntax_node2(x_922, x_930, x_927, x_929);
x_932 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_922);
x_933 = l_Lean_Syntax_node1(x_922, x_932, x_931);
x_934 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_922);
x_935 = l_Lean_Syntax_node1(x_922, x_934, x_933);
x_936 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_922);
x_937 = l_Lean_Syntax_node2(x_922, x_936, x_935, x_902);
x_938 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_939 = l_Lean_Syntax_node1(x_922, x_938, x_937);
x_940 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_939, x_7, x_8, x_9, x_10, x_924);
x_16 = x_940;
goto block_21;
}
case 2:
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_941 = lean_ctor_get(x_9, 5);
lean_inc(x_941);
x_942 = l_Lean_SourceInfo_fromRef(x_941, x_897);
lean_dec(x_941);
x_943 = lean_st_ref_get(x_10, x_900);
x_944 = lean_ctor_get(x_943, 1);
lean_inc(x_944);
if (lean_is_exclusive(x_943)) {
 lean_ctor_release(x_943, 0);
 lean_ctor_release(x_943, 1);
 x_945 = x_943;
} else {
 lean_dec_ref(x_943);
 x_945 = lean_box(0);
}
x_946 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_942);
if (lean_is_scalar(x_945)) {
 x_947 = lean_alloc_ctor(2, 2, 0);
} else {
 x_947 = x_945;
 lean_ctor_set_tag(x_947, 2);
}
lean_ctor_set(x_947, 0, x_942);
lean_ctor_set(x_947, 1, x_946);
x_948 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_942);
if (lean_is_scalar(x_901)) {
 x_949 = lean_alloc_ctor(2, 2, 0);
} else {
 x_949 = x_901;
 lean_ctor_set_tag(x_949, 2);
}
lean_ctor_set(x_949, 0, x_942);
lean_ctor_set(x_949, 1, x_948);
x_950 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_inc(x_947);
lean_inc(x_942);
x_951 = l_Lean_Syntax_node3(x_942, x_950, x_947, x_949, x_947);
x_952 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_942);
x_953 = l_Lean_Syntax_node1(x_942, x_952, x_951);
x_954 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_942);
x_955 = l_Lean_Syntax_node1(x_942, x_954, x_953);
x_956 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_942);
x_957 = l_Lean_Syntax_node2(x_942, x_956, x_955, x_902);
x_958 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_959 = l_Lean_Syntax_node1(x_942, x_958, x_957);
x_960 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_959, x_7, x_8, x_9, x_10, x_944);
x_16 = x_960;
goto block_21;
}
case 3:
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_961 = lean_ctor_get(x_9, 5);
lean_inc(x_961);
x_962 = l_Lean_SourceInfo_fromRef(x_961, x_897);
lean_dec(x_961);
x_963 = lean_st_ref_get(x_10, x_900);
x_964 = lean_ctor_get(x_963, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_965 = x_963;
} else {
 lean_dec_ref(x_963);
 x_965 = lean_box(0);
}
x_966 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_962);
if (lean_is_scalar(x_965)) {
 x_967 = lean_alloc_ctor(2, 2, 0);
} else {
 x_967 = x_965;
 lean_ctor_set_tag(x_967, 2);
}
lean_ctor_set(x_967, 0, x_962);
lean_ctor_set(x_967, 1, x_966);
x_968 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_962);
if (lean_is_scalar(x_901)) {
 x_969 = lean_alloc_ctor(2, 2, 0);
} else {
 x_969 = x_901;
 lean_ctor_set_tag(x_969, 2);
}
lean_ctor_set(x_969, 0, x_962);
lean_ctor_set(x_969, 1, x_968);
x_970 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
lean_inc(x_962);
x_971 = l_Lean_Syntax_node2(x_962, x_970, x_967, x_969);
x_972 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
lean_inc(x_962);
x_973 = l_Lean_Syntax_node1(x_962, x_972, x_971);
x_974 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_962);
x_975 = l_Lean_Syntax_node1(x_962, x_974, x_973);
x_976 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_962);
x_977 = l_Lean_Syntax_node1(x_962, x_976, x_975);
x_978 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_962);
x_979 = l_Lean_Syntax_node2(x_962, x_978, x_977, x_902);
x_980 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_981 = l_Lean_Syntax_node1(x_962, x_980, x_979);
x_982 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_981, x_7, x_8, x_9, x_10, x_964);
x_16 = x_982;
goto block_21;
}
case 4:
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_901);
x_983 = lean_ctor_get(x_9, 5);
lean_inc(x_983);
x_984 = l_Lean_SourceInfo_fromRef(x_983, x_897);
lean_dec(x_983);
x_985 = lean_st_ref_get(x_10, x_900);
x_986 = lean_ctor_get(x_985, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_985)) {
 lean_ctor_release(x_985, 0);
 lean_ctor_release(x_985, 1);
 x_987 = x_985;
} else {
 lean_dec_ref(x_985);
 x_987 = lean_box(0);
}
x_988 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
lean_inc(x_984);
if (lean_is_scalar(x_987)) {
 x_989 = lean_alloc_ctor(2, 2, 0);
} else {
 x_989 = x_987;
 lean_ctor_set_tag(x_989, 2);
}
lean_ctor_set(x_989, 0, x_984);
lean_ctor_set(x_989, 1, x_988);
x_990 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_inc(x_984);
x_991 = l_Lean_Syntax_node1(x_984, x_990, x_989);
x_992 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_inc(x_984);
x_993 = l_Lean_Syntax_node1(x_984, x_992, x_991);
x_994 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_984);
x_995 = l_Lean_Syntax_node1(x_984, x_994, x_993);
x_996 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_984);
x_997 = l_Lean_Syntax_node1(x_984, x_996, x_995);
x_998 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_984);
x_999 = l_Lean_Syntax_node2(x_984, x_998, x_997, x_902);
x_1000 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1001 = l_Lean_Syntax_node1(x_984, x_1000, x_999);
x_1002 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_1001, x_7, x_8, x_9, x_10, x_986);
x_16 = x_1002;
goto block_21;
}
case 5:
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; 
lean_dec(x_901);
x_1003 = lean_ctor_get(x_9, 5);
lean_inc(x_1003);
x_1004 = l_Lean_SourceInfo_fromRef(x_1003, x_897);
lean_dec(x_1003);
x_1005 = lean_st_ref_get(x_10, x_900);
x_1006 = lean_ctor_get(x_1005, 1);
lean_inc(x_1006);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 x_1007 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1007 = lean_box(0);
}
x_1008 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_1004);
if (lean_is_scalar(x_1007)) {
 x_1009 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1009 = x_1007;
 lean_ctor_set_tag(x_1009, 2);
}
lean_ctor_set(x_1009, 0, x_1004);
lean_ctor_set(x_1009, 1, x_1008);
x_1010 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
lean_inc(x_1004);
x_1011 = l_Lean_Syntax_node1(x_1004, x_1010, x_1009);
x_1012 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
lean_inc(x_1004);
x_1013 = l_Lean_Syntax_node1(x_1004, x_1012, x_1011);
x_1014 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1004);
x_1015 = l_Lean_Syntax_node1(x_1004, x_1014, x_1013);
x_1016 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1004);
x_1017 = l_Lean_Syntax_node1(x_1004, x_1016, x_1015);
x_1018 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1004);
x_1019 = l_Lean_Syntax_node2(x_1004, x_1018, x_1017, x_902);
x_1020 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1021 = l_Lean_Syntax_node1(x_1004, x_1020, x_1019);
x_1022 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_1021, x_7, x_8, x_9, x_10, x_1006);
x_16 = x_1022;
goto block_21;
}
case 6:
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
lean_dec(x_901);
x_1023 = lean_ctor_get(x_9, 5);
lean_inc(x_1023);
x_1024 = l_Lean_SourceInfo_fromRef(x_1023, x_897);
lean_dec(x_1023);
x_1025 = lean_st_ref_get(x_10, x_900);
x_1026 = lean_ctor_get(x_1025, 1);
lean_inc(x_1026);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 lean_ctor_release(x_1025, 1);
 x_1027 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1027 = lean_box(0);
}
x_1028 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
lean_inc(x_1024);
if (lean_is_scalar(x_1027)) {
 x_1029 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1029 = x_1027;
 lean_ctor_set_tag(x_1029, 2);
}
lean_ctor_set(x_1029, 0, x_1024);
lean_ctor_set(x_1029, 1, x_1028);
x_1030 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
lean_inc(x_1024);
x_1031 = l_Lean_Syntax_node1(x_1024, x_1030, x_1029);
x_1032 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
lean_inc(x_1024);
x_1033 = l_Lean_Syntax_node1(x_1024, x_1032, x_1031);
x_1034 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1024);
x_1035 = l_Lean_Syntax_node1(x_1024, x_1034, x_1033);
x_1036 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1024);
x_1037 = l_Lean_Syntax_node1(x_1024, x_1036, x_1035);
x_1038 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1024);
x_1039 = l_Lean_Syntax_node2(x_1024, x_1038, x_1037, x_902);
x_1040 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1041 = l_Lean_Syntax_node1(x_1024, x_1040, x_1039);
x_1042 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_1041, x_7, x_8, x_9, x_10, x_1026);
x_16 = x_1042;
goto block_21;
}
case 7:
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
lean_dec(x_901);
x_1043 = lean_ctor_get(x_9, 5);
lean_inc(x_1043);
x_1044 = l_Lean_SourceInfo_fromRef(x_1043, x_897);
lean_dec(x_1043);
x_1045 = lean_st_ref_get(x_10, x_900);
x_1046 = lean_ctor_get(x_1045, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 lean_ctor_release(x_1045, 1);
 x_1047 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1047 = lean_box(0);
}
x_1048 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
lean_inc(x_1044);
if (lean_is_scalar(x_1047)) {
 x_1049 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1049 = x_1047;
 lean_ctor_set_tag(x_1049, 2);
}
lean_ctor_set(x_1049, 0, x_1044);
lean_ctor_set(x_1049, 1, x_1048);
x_1050 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_inc(x_1044);
x_1051 = l_Lean_Syntax_node1(x_1044, x_1050, x_1049);
x_1052 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
lean_inc(x_1044);
x_1053 = l_Lean_Syntax_node1(x_1044, x_1052, x_1051);
x_1054 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1044);
x_1055 = l_Lean_Syntax_node1(x_1044, x_1054, x_1053);
x_1056 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1044);
x_1057 = l_Lean_Syntax_node1(x_1044, x_1056, x_1055);
x_1058 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1044);
x_1059 = l_Lean_Syntax_node2(x_1044, x_1058, x_1057, x_902);
x_1060 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1061 = l_Lean_Syntax_node1(x_1044, x_1060, x_1059);
x_1062 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_1061, x_7, x_8, x_9, x_10, x_1046);
x_16 = x_1062;
goto block_21;
}
case 8:
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
lean_dec(x_901);
x_1063 = lean_ctor_get(x_9, 5);
lean_inc(x_1063);
x_1064 = l_Lean_SourceInfo_fromRef(x_1063, x_897);
lean_dec(x_1063);
x_1065 = lean_st_ref_get(x_10, x_900);
x_1066 = lean_ctor_get(x_1065, 1);
lean_inc(x_1066);
lean_dec(x_1065);
x_1067 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_1068 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_1064);
x_1069 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1069, 0, x_1064);
lean_ctor_set(x_1069, 1, x_1067);
lean_ctor_set(x_1069, 2, x_1068);
x_1070 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1064);
x_1071 = l_Lean_Syntax_node2(x_1064, x_1070, x_1069, x_902);
x_1072 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1073 = l_Lean_Syntax_node1(x_1064, x_1072, x_1071);
x_1074 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_1073, x_7, x_8, x_9, x_10, x_1066);
x_16 = x_1074;
goto block_21;
}
default: 
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_901);
x_1075 = lean_ctor_get(x_9, 5);
lean_inc(x_1075);
x_1076 = l_Lean_SourceInfo_fromRef(x_1075, x_897);
lean_dec(x_1075);
x_1077 = lean_st_ref_get(x_10, x_900);
x_1078 = lean_ctor_get(x_1077, 1);
lean_inc(x_1078);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1079 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1079 = lean_box(0);
}
x_1080 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
lean_inc(x_1076);
if (lean_is_scalar(x_1079)) {
 x_1081 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1081 = x_1079;
 lean_ctor_set_tag(x_1081, 2);
}
lean_ctor_set(x_1081, 0, x_1076);
lean_ctor_set(x_1081, 1, x_1080);
x_1082 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
lean_inc(x_1076);
x_1083 = l_Lean_Syntax_node1(x_1076, x_1082, x_1081);
x_1084 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1076);
x_1085 = l_Lean_Syntax_node1(x_1076, x_1084, x_1083);
x_1086 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1076);
x_1087 = l_Lean_Syntax_node1(x_1076, x_1086, x_1085);
x_1088 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1076);
x_1089 = l_Lean_Syntax_node2(x_1076, x_1088, x_1087, x_902);
x_1090 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1091 = l_Lean_Syntax_node1(x_1076, x_1090, x_1089);
x_1092 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_885, x_886, x_1091, x_7, x_8, x_9, x_10, x_1078);
x_16 = x_1092;
goto block_21;
}
}
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; 
lean_dec(x_887);
x_1093 = lean_ctor_get(x_894, 1);
lean_inc(x_1093);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_1094 = x_894;
} else {
 lean_dec_ref(x_894);
 x_1094 = lean_box(0);
}
x_1095 = lean_ctor_get(x_895, 0);
lean_inc(x_1095);
if (lean_is_exclusive(x_895)) {
 lean_ctor_release(x_895, 0);
 x_1096 = x_895;
} else {
 lean_dec_ref(x_895);
 x_1096 = lean_box(0);
}
x_1097 = l_Lean_NameSet_contains(x_885, x_1095);
if (x_1097 == 0)
{
lean_object* x_1098; lean_object* x_1099; uint8_t x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
lean_dec(x_1094);
x_1098 = lean_box(0);
lean_inc(x_1095);
x_1099 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_885, x_1095, x_1098);
x_1100 = 0;
lean_inc(x_9);
x_1101 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_1095, x_1100, x_7, x_8, x_9, x_10, x_1093);
x_1102 = lean_ctor_get(x_1101, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1101, 1);
lean_inc(x_1103);
lean_dec(x_1101);
x_1104 = lean_mk_syntax_ident(x_1102);
x_1105 = lean_ctor_get(x_9, 5);
lean_inc(x_1105);
x_1106 = l_Lean_SourceInfo_fromRef(x_1105, x_1100);
lean_dec(x_1105);
x_1107 = lean_st_ref_get(x_10, x_1103);
x_1108 = lean_ctor_get(x_1107, 1);
lean_inc(x_1108);
if (lean_is_exclusive(x_1107)) {
 lean_ctor_release(x_1107, 0);
 lean_ctor_release(x_1107, 1);
 x_1109 = x_1107;
} else {
 lean_dec_ref(x_1107);
 x_1109 = lean_box(0);
}
x_1110 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_1111 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_1106);
x_1112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1112, 0, x_1106);
lean_ctor_set(x_1112, 1, x_1110);
lean_ctor_set(x_1112, 2, x_1111);
x_1113 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1106);
x_1114 = l_Lean_Syntax_node2(x_1106, x_1113, x_1112, x_1104);
x_1115 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1116 = l_Lean_Syntax_node1(x_1106, x_1115, x_1114);
x_1117 = lean_array_push(x_886, x_1116);
lean_ctor_set(x_5, 1, x_1117);
lean_ctor_set(x_5, 0, x_1099);
if (lean_is_scalar(x_1096)) {
 x_1118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1118 = x_1096;
}
lean_ctor_set(x_1118, 0, x_5);
if (lean_is_scalar(x_1109)) {
 x_1119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1119 = x_1109;
}
lean_ctor_set(x_1119, 0, x_1118);
lean_ctor_set(x_1119, 1, x_1108);
x_16 = x_1119;
goto block_21;
}
else
{
lean_object* x_1120; lean_object* x_1121; 
lean_dec(x_1095);
if (lean_is_scalar(x_1096)) {
 x_1120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1120 = x_1096;
}
lean_ctor_set(x_1120, 0, x_5);
if (lean_is_scalar(x_1094)) {
 x_1121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1121 = x_1094;
}
lean_ctor_set(x_1121, 0, x_1120);
lean_ctor_set(x_1121, 1, x_1093);
x_16 = x_1121;
goto block_21;
}
}
}
else
{
lean_object* x_1122; lean_object* x_1123; 
lean_dec(x_887);
x_1122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1122, 0, x_5);
if (lean_is_scalar(x_891)) {
 x_1123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1123 = x_891;
}
lean_ctor_set(x_1123, 0, x_1122);
lean_ctor_set(x_1123, 1, x_890);
x_16 = x_1123;
goto block_21;
}
}
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; uint8_t x_1133; 
x_1124 = lean_ctor_get(x_5, 0);
x_1125 = lean_ctor_get(x_5, 1);
lean_inc(x_1125);
lean_inc(x_1124);
lean_dec(x_5);
x_1126 = lean_ctor_get(x_22, 0);
lean_inc(x_1126);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_1127 = x_22;
} else {
 lean_dec_ref(x_22);
 x_1127 = lean_box(0);
}
x_1128 = lean_st_ref_get(x_10, x_11);
x_1129 = lean_ctor_get(x_1128, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1128, 1);
lean_inc(x_1130);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1131 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1131 = lean_box(0);
}
x_1132 = lean_ctor_get(x_1129, 0);
lean_inc(x_1132);
lean_dec(x_1129);
x_1133 = l_Lean_Meta_Match_isMatchEqnTheorem(x_1132, x_1126);
if (x_1133 == 0)
{
lean_object* x_1134; lean_object* x_1135; 
lean_dec(x_1131);
lean_dec(x_1127);
x_1134 = l_Lean_Meta_isEqnThm_x3f(x_1126, x_9, x_10, x_1130);
x_1135 = lean_ctor_get(x_1134, 0);
lean_inc(x_1135);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; uint8_t x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1136 = lean_ctor_get(x_1134, 1);
lean_inc(x_1136);
lean_dec(x_1134);
x_1137 = 0;
lean_inc(x_9);
x_1138 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_1126, x_1137, x_7, x_8, x_9, x_10, x_1136);
x_1139 = lean_ctor_get(x_1138, 0);
lean_inc(x_1139);
x_1140 = lean_ctor_get(x_1138, 1);
lean_inc(x_1140);
if (lean_is_exclusive(x_1138)) {
 lean_ctor_release(x_1138, 0);
 lean_ctor_release(x_1138, 1);
 x_1141 = x_1138;
} else {
 lean_dec_ref(x_1138);
 x_1141 = lean_box(0);
}
x_1142 = lean_mk_syntax_ident(x_1139);
switch (x_23) {
case 0:
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
lean_dec(x_1141);
x_1143 = lean_ctor_get(x_9, 5);
lean_inc(x_1143);
x_1144 = l_Lean_SourceInfo_fromRef(x_1143, x_1137);
lean_dec(x_1143);
x_1145 = lean_st_ref_get(x_10, x_1140);
x_1146 = lean_ctor_get(x_1145, 1);
lean_inc(x_1146);
if (lean_is_exclusive(x_1145)) {
 lean_ctor_release(x_1145, 0);
 lean_ctor_release(x_1145, 1);
 x_1147 = x_1145;
} else {
 lean_dec_ref(x_1145);
 x_1147 = lean_box(0);
}
x_1148 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1144);
if (lean_is_scalar(x_1147)) {
 x_1149 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1149 = x_1147;
 lean_ctor_set_tag(x_1149, 2);
}
lean_ctor_set(x_1149, 0, x_1144);
lean_ctor_set(x_1149, 1, x_1148);
x_1150 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
lean_inc(x_1144);
x_1151 = l_Lean_Syntax_node1(x_1144, x_1150, x_1149);
x_1152 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1144);
x_1153 = l_Lean_Syntax_node1(x_1144, x_1152, x_1151);
x_1154 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1144);
x_1155 = l_Lean_Syntax_node1(x_1144, x_1154, x_1153);
x_1156 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1144);
x_1157 = l_Lean_Syntax_node2(x_1144, x_1156, x_1155, x_1142);
x_1158 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1159 = l_Lean_Syntax_node1(x_1144, x_1158, x_1157);
x_1160 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1159, x_7, x_8, x_9, x_10, x_1146);
x_16 = x_1160;
goto block_21;
}
case 1:
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
x_1161 = lean_ctor_get(x_9, 5);
lean_inc(x_1161);
x_1162 = l_Lean_SourceInfo_fromRef(x_1161, x_1137);
lean_dec(x_1161);
x_1163 = lean_st_ref_get(x_10, x_1140);
x_1164 = lean_ctor_get(x_1163, 1);
lean_inc(x_1164);
if (lean_is_exclusive(x_1163)) {
 lean_ctor_release(x_1163, 0);
 lean_ctor_release(x_1163, 1);
 x_1165 = x_1163;
} else {
 lean_dec_ref(x_1163);
 x_1165 = lean_box(0);
}
x_1166 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1162);
if (lean_is_scalar(x_1165)) {
 x_1167 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1167 = x_1165;
 lean_ctor_set_tag(x_1167, 2);
}
lean_ctor_set(x_1167, 0, x_1162);
lean_ctor_set(x_1167, 1, x_1166);
x_1168 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_1162);
if (lean_is_scalar(x_1141)) {
 x_1169 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1169 = x_1141;
 lean_ctor_set_tag(x_1169, 2);
}
lean_ctor_set(x_1169, 0, x_1162);
lean_ctor_set(x_1169, 1, x_1168);
x_1170 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
lean_inc(x_1162);
x_1171 = l_Lean_Syntax_node2(x_1162, x_1170, x_1167, x_1169);
x_1172 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1162);
x_1173 = l_Lean_Syntax_node1(x_1162, x_1172, x_1171);
x_1174 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1162);
x_1175 = l_Lean_Syntax_node1(x_1162, x_1174, x_1173);
x_1176 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1162);
x_1177 = l_Lean_Syntax_node2(x_1162, x_1176, x_1175, x_1142);
x_1178 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1179 = l_Lean_Syntax_node1(x_1162, x_1178, x_1177);
x_1180 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1179, x_7, x_8, x_9, x_10, x_1164);
x_16 = x_1180;
goto block_21;
}
case 2:
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
x_1181 = lean_ctor_get(x_9, 5);
lean_inc(x_1181);
x_1182 = l_Lean_SourceInfo_fromRef(x_1181, x_1137);
lean_dec(x_1181);
x_1183 = lean_st_ref_get(x_10, x_1140);
x_1184 = lean_ctor_get(x_1183, 1);
lean_inc(x_1184);
if (lean_is_exclusive(x_1183)) {
 lean_ctor_release(x_1183, 0);
 lean_ctor_release(x_1183, 1);
 x_1185 = x_1183;
} else {
 lean_dec_ref(x_1183);
 x_1185 = lean_box(0);
}
x_1186 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_1182);
if (lean_is_scalar(x_1185)) {
 x_1187 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1187 = x_1185;
 lean_ctor_set_tag(x_1187, 2);
}
lean_ctor_set(x_1187, 0, x_1182);
lean_ctor_set(x_1187, 1, x_1186);
x_1188 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1182);
if (lean_is_scalar(x_1141)) {
 x_1189 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1189 = x_1141;
 lean_ctor_set_tag(x_1189, 2);
}
lean_ctor_set(x_1189, 0, x_1182);
lean_ctor_set(x_1189, 1, x_1188);
x_1190 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_inc(x_1187);
lean_inc(x_1182);
x_1191 = l_Lean_Syntax_node3(x_1182, x_1190, x_1187, x_1189, x_1187);
x_1192 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1182);
x_1193 = l_Lean_Syntax_node1(x_1182, x_1192, x_1191);
x_1194 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1182);
x_1195 = l_Lean_Syntax_node1(x_1182, x_1194, x_1193);
x_1196 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1182);
x_1197 = l_Lean_Syntax_node2(x_1182, x_1196, x_1195, x_1142);
x_1198 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1199 = l_Lean_Syntax_node1(x_1182, x_1198, x_1197);
x_1200 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1199, x_7, x_8, x_9, x_10, x_1184);
x_16 = x_1200;
goto block_21;
}
case 3:
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
x_1201 = lean_ctor_get(x_9, 5);
lean_inc(x_1201);
x_1202 = l_Lean_SourceInfo_fromRef(x_1201, x_1137);
lean_dec(x_1201);
x_1203 = lean_st_ref_get(x_10, x_1140);
x_1204 = lean_ctor_get(x_1203, 1);
lean_inc(x_1204);
if (lean_is_exclusive(x_1203)) {
 lean_ctor_release(x_1203, 0);
 lean_ctor_release(x_1203, 1);
 x_1205 = x_1203;
} else {
 lean_dec_ref(x_1203);
 x_1205 = lean_box(0);
}
x_1206 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_1202);
if (lean_is_scalar(x_1205)) {
 x_1207 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1207 = x_1205;
 lean_ctor_set_tag(x_1207, 2);
}
lean_ctor_set(x_1207, 0, x_1202);
lean_ctor_set(x_1207, 1, x_1206);
x_1208 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1202);
if (lean_is_scalar(x_1141)) {
 x_1209 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1209 = x_1141;
 lean_ctor_set_tag(x_1209, 2);
}
lean_ctor_set(x_1209, 0, x_1202);
lean_ctor_set(x_1209, 1, x_1208);
x_1210 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
lean_inc(x_1202);
x_1211 = l_Lean_Syntax_node2(x_1202, x_1210, x_1207, x_1209);
x_1212 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
lean_inc(x_1202);
x_1213 = l_Lean_Syntax_node1(x_1202, x_1212, x_1211);
x_1214 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1202);
x_1215 = l_Lean_Syntax_node1(x_1202, x_1214, x_1213);
x_1216 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1202);
x_1217 = l_Lean_Syntax_node1(x_1202, x_1216, x_1215);
x_1218 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1202);
x_1219 = l_Lean_Syntax_node2(x_1202, x_1218, x_1217, x_1142);
x_1220 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1221 = l_Lean_Syntax_node1(x_1202, x_1220, x_1219);
x_1222 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1221, x_7, x_8, x_9, x_10, x_1204);
x_16 = x_1222;
goto block_21;
}
case 4:
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
lean_dec(x_1141);
x_1223 = lean_ctor_get(x_9, 5);
lean_inc(x_1223);
x_1224 = l_Lean_SourceInfo_fromRef(x_1223, x_1137);
lean_dec(x_1223);
x_1225 = lean_st_ref_get(x_10, x_1140);
x_1226 = lean_ctor_get(x_1225, 1);
lean_inc(x_1226);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 lean_ctor_release(x_1225, 1);
 x_1227 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1227 = lean_box(0);
}
x_1228 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
lean_inc(x_1224);
if (lean_is_scalar(x_1227)) {
 x_1229 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1229 = x_1227;
 lean_ctor_set_tag(x_1229, 2);
}
lean_ctor_set(x_1229, 0, x_1224);
lean_ctor_set(x_1229, 1, x_1228);
x_1230 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_inc(x_1224);
x_1231 = l_Lean_Syntax_node1(x_1224, x_1230, x_1229);
x_1232 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_inc(x_1224);
x_1233 = l_Lean_Syntax_node1(x_1224, x_1232, x_1231);
x_1234 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1224);
x_1235 = l_Lean_Syntax_node1(x_1224, x_1234, x_1233);
x_1236 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1224);
x_1237 = l_Lean_Syntax_node1(x_1224, x_1236, x_1235);
x_1238 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1224);
x_1239 = l_Lean_Syntax_node2(x_1224, x_1238, x_1237, x_1142);
x_1240 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1241 = l_Lean_Syntax_node1(x_1224, x_1240, x_1239);
x_1242 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1241, x_7, x_8, x_9, x_10, x_1226);
x_16 = x_1242;
goto block_21;
}
case 5:
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
lean_dec(x_1141);
x_1243 = lean_ctor_get(x_9, 5);
lean_inc(x_1243);
x_1244 = l_Lean_SourceInfo_fromRef(x_1243, x_1137);
lean_dec(x_1243);
x_1245 = lean_st_ref_get(x_10, x_1140);
x_1246 = lean_ctor_get(x_1245, 1);
lean_inc(x_1246);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1247 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1247 = lean_box(0);
}
x_1248 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_1244);
if (lean_is_scalar(x_1247)) {
 x_1249 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1249 = x_1247;
 lean_ctor_set_tag(x_1249, 2);
}
lean_ctor_set(x_1249, 0, x_1244);
lean_ctor_set(x_1249, 1, x_1248);
x_1250 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
lean_inc(x_1244);
x_1251 = l_Lean_Syntax_node1(x_1244, x_1250, x_1249);
x_1252 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
lean_inc(x_1244);
x_1253 = l_Lean_Syntax_node1(x_1244, x_1252, x_1251);
x_1254 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1244);
x_1255 = l_Lean_Syntax_node1(x_1244, x_1254, x_1253);
x_1256 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1244);
x_1257 = l_Lean_Syntax_node1(x_1244, x_1256, x_1255);
x_1258 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1244);
x_1259 = l_Lean_Syntax_node2(x_1244, x_1258, x_1257, x_1142);
x_1260 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1261 = l_Lean_Syntax_node1(x_1244, x_1260, x_1259);
x_1262 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1261, x_7, x_8, x_9, x_10, x_1246);
x_16 = x_1262;
goto block_21;
}
case 6:
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_1141);
x_1263 = lean_ctor_get(x_9, 5);
lean_inc(x_1263);
x_1264 = l_Lean_SourceInfo_fromRef(x_1263, x_1137);
lean_dec(x_1263);
x_1265 = lean_st_ref_get(x_10, x_1140);
x_1266 = lean_ctor_get(x_1265, 1);
lean_inc(x_1266);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 x_1267 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1267 = lean_box(0);
}
x_1268 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
lean_inc(x_1264);
if (lean_is_scalar(x_1267)) {
 x_1269 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1269 = x_1267;
 lean_ctor_set_tag(x_1269, 2);
}
lean_ctor_set(x_1269, 0, x_1264);
lean_ctor_set(x_1269, 1, x_1268);
x_1270 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
lean_inc(x_1264);
x_1271 = l_Lean_Syntax_node1(x_1264, x_1270, x_1269);
x_1272 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
lean_inc(x_1264);
x_1273 = l_Lean_Syntax_node1(x_1264, x_1272, x_1271);
x_1274 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1264);
x_1275 = l_Lean_Syntax_node1(x_1264, x_1274, x_1273);
x_1276 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1264);
x_1277 = l_Lean_Syntax_node1(x_1264, x_1276, x_1275);
x_1278 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1264);
x_1279 = l_Lean_Syntax_node2(x_1264, x_1278, x_1277, x_1142);
x_1280 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1281 = l_Lean_Syntax_node1(x_1264, x_1280, x_1279);
x_1282 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1281, x_7, x_8, x_9, x_10, x_1266);
x_16 = x_1282;
goto block_21;
}
case 7:
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
lean_dec(x_1141);
x_1283 = lean_ctor_get(x_9, 5);
lean_inc(x_1283);
x_1284 = l_Lean_SourceInfo_fromRef(x_1283, x_1137);
lean_dec(x_1283);
x_1285 = lean_st_ref_get(x_10, x_1140);
x_1286 = lean_ctor_get(x_1285, 1);
lean_inc(x_1286);
if (lean_is_exclusive(x_1285)) {
 lean_ctor_release(x_1285, 0);
 lean_ctor_release(x_1285, 1);
 x_1287 = x_1285;
} else {
 lean_dec_ref(x_1285);
 x_1287 = lean_box(0);
}
x_1288 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
lean_inc(x_1284);
if (lean_is_scalar(x_1287)) {
 x_1289 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1289 = x_1287;
 lean_ctor_set_tag(x_1289, 2);
}
lean_ctor_set(x_1289, 0, x_1284);
lean_ctor_set(x_1289, 1, x_1288);
x_1290 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_inc(x_1284);
x_1291 = l_Lean_Syntax_node1(x_1284, x_1290, x_1289);
x_1292 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
lean_inc(x_1284);
x_1293 = l_Lean_Syntax_node1(x_1284, x_1292, x_1291);
x_1294 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1284);
x_1295 = l_Lean_Syntax_node1(x_1284, x_1294, x_1293);
x_1296 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1284);
x_1297 = l_Lean_Syntax_node1(x_1284, x_1296, x_1295);
x_1298 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1284);
x_1299 = l_Lean_Syntax_node2(x_1284, x_1298, x_1297, x_1142);
x_1300 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1301 = l_Lean_Syntax_node1(x_1284, x_1300, x_1299);
x_1302 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1301, x_7, x_8, x_9, x_10, x_1286);
x_16 = x_1302;
goto block_21;
}
case 8:
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1141);
x_1303 = lean_ctor_get(x_9, 5);
lean_inc(x_1303);
x_1304 = l_Lean_SourceInfo_fromRef(x_1303, x_1137);
lean_dec(x_1303);
x_1305 = lean_st_ref_get(x_10, x_1140);
x_1306 = lean_ctor_get(x_1305, 1);
lean_inc(x_1306);
lean_dec(x_1305);
x_1307 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_1308 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_1304);
x_1309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1309, 0, x_1304);
lean_ctor_set(x_1309, 1, x_1307);
lean_ctor_set(x_1309, 2, x_1308);
x_1310 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1304);
x_1311 = l_Lean_Syntax_node2(x_1304, x_1310, x_1309, x_1142);
x_1312 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1313 = l_Lean_Syntax_node1(x_1304, x_1312, x_1311);
x_1314 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1313, x_7, x_8, x_9, x_10, x_1306);
x_16 = x_1314;
goto block_21;
}
default: 
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
lean_dec(x_1141);
x_1315 = lean_ctor_get(x_9, 5);
lean_inc(x_1315);
x_1316 = l_Lean_SourceInfo_fromRef(x_1315, x_1137);
lean_dec(x_1315);
x_1317 = lean_st_ref_get(x_10, x_1140);
x_1318 = lean_ctor_get(x_1317, 1);
lean_inc(x_1318);
if (lean_is_exclusive(x_1317)) {
 lean_ctor_release(x_1317, 0);
 lean_ctor_release(x_1317, 1);
 x_1319 = x_1317;
} else {
 lean_dec_ref(x_1317);
 x_1319 = lean_box(0);
}
x_1320 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
lean_inc(x_1316);
if (lean_is_scalar(x_1319)) {
 x_1321 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1321 = x_1319;
 lean_ctor_set_tag(x_1321, 2);
}
lean_ctor_set(x_1321, 0, x_1316);
lean_ctor_set(x_1321, 1, x_1320);
x_1322 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
lean_inc(x_1316);
x_1323 = l_Lean_Syntax_node1(x_1316, x_1322, x_1321);
x_1324 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1316);
x_1325 = l_Lean_Syntax_node1(x_1316, x_1324, x_1323);
x_1326 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1316);
x_1327 = l_Lean_Syntax_node1(x_1316, x_1326, x_1325);
x_1328 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1316);
x_1329 = l_Lean_Syntax_node2(x_1316, x_1328, x_1327, x_1142);
x_1330 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1331 = l_Lean_Syntax_node1(x_1316, x_1330, x_1329);
x_1332 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1124, x_1125, x_1331, x_7, x_8, x_9, x_10, x_1318);
x_16 = x_1332;
goto block_21;
}
}
}
else
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; uint8_t x_1337; 
lean_dec(x_1126);
x_1333 = lean_ctor_get(x_1134, 1);
lean_inc(x_1333);
if (lean_is_exclusive(x_1134)) {
 lean_ctor_release(x_1134, 0);
 lean_ctor_release(x_1134, 1);
 x_1334 = x_1134;
} else {
 lean_dec_ref(x_1134);
 x_1334 = lean_box(0);
}
x_1335 = lean_ctor_get(x_1135, 0);
lean_inc(x_1335);
if (lean_is_exclusive(x_1135)) {
 lean_ctor_release(x_1135, 0);
 x_1336 = x_1135;
} else {
 lean_dec_ref(x_1135);
 x_1336 = lean_box(0);
}
x_1337 = l_Lean_NameSet_contains(x_1124, x_1335);
if (x_1337 == 0)
{
lean_object* x_1338; lean_object* x_1339; uint8_t x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
lean_dec(x_1334);
x_1338 = lean_box(0);
lean_inc(x_1335);
x_1339 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1124, x_1335, x_1338);
x_1340 = 0;
lean_inc(x_9);
x_1341 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_1335, x_1340, x_7, x_8, x_9, x_10, x_1333);
x_1342 = lean_ctor_get(x_1341, 0);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1341, 1);
lean_inc(x_1343);
lean_dec(x_1341);
x_1344 = lean_mk_syntax_ident(x_1342);
x_1345 = lean_ctor_get(x_9, 5);
lean_inc(x_1345);
x_1346 = l_Lean_SourceInfo_fromRef(x_1345, x_1340);
lean_dec(x_1345);
x_1347 = lean_st_ref_get(x_10, x_1343);
x_1348 = lean_ctor_get(x_1347, 1);
lean_inc(x_1348);
if (lean_is_exclusive(x_1347)) {
 lean_ctor_release(x_1347, 0);
 lean_ctor_release(x_1347, 1);
 x_1349 = x_1347;
} else {
 lean_dec_ref(x_1347);
 x_1349 = lean_box(0);
}
x_1350 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_1351 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_1346);
x_1352 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1352, 0, x_1346);
lean_ctor_set(x_1352, 1, x_1350);
lean_ctor_set(x_1352, 2, x_1351);
x_1353 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1346);
x_1354 = l_Lean_Syntax_node2(x_1346, x_1353, x_1352, x_1344);
x_1355 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1356 = l_Lean_Syntax_node1(x_1346, x_1355, x_1354);
x_1357 = lean_array_push(x_1125, x_1356);
x_1358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1358, 0, x_1339);
lean_ctor_set(x_1358, 1, x_1357);
if (lean_is_scalar(x_1336)) {
 x_1359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1359 = x_1336;
}
lean_ctor_set(x_1359, 0, x_1358);
if (lean_is_scalar(x_1349)) {
 x_1360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1360 = x_1349;
}
lean_ctor_set(x_1360, 0, x_1359);
lean_ctor_set(x_1360, 1, x_1348);
x_16 = x_1360;
goto block_21;
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
lean_dec(x_1335);
x_1361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1361, 0, x_1124);
lean_ctor_set(x_1361, 1, x_1125);
if (lean_is_scalar(x_1336)) {
 x_1362 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1362 = x_1336;
}
lean_ctor_set(x_1362, 0, x_1361);
if (lean_is_scalar(x_1334)) {
 x_1363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1363 = x_1334;
}
lean_ctor_set(x_1363, 0, x_1362);
lean_ctor_set(x_1363, 1, x_1333);
x_16 = x_1363;
goto block_21;
}
}
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
lean_dec(x_1126);
x_1364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1364, 0, x_1124);
lean_ctor_set(x_1364, 1, x_1125);
if (lean_is_scalar(x_1127)) {
 x_1365 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1365 = x_1127;
 lean_ctor_set_tag(x_1365, 1);
}
lean_ctor_set(x_1365, 0, x_1364);
if (lean_is_scalar(x_1131)) {
 x_1366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1366 = x_1131;
}
lean_ctor_set(x_1366, 0, x_1365);
lean_ctor_set(x_1366, 1, x_1130);
x_16 = x_1366;
goto block_21;
}
}
}
case 1:
{
uint8_t x_1367; 
lean_dec(x_14);
x_1367 = !lean_is_exclusive(x_22);
if (x_1367 == 0)
{
lean_object* x_1368; uint8_t x_1369; 
x_1368 = lean_ctor_get(x_22, 0);
lean_dec(x_1368);
x_1369 = !lean_is_exclusive(x_5);
if (x_1369 == 0)
{
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_22);
x_16 = x_4;
goto block_21;
}
else
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
x_1370 = lean_ctor_get(x_5, 0);
x_1371 = lean_ctor_get(x_5, 1);
lean_inc(x_1371);
lean_inc(x_1370);
lean_dec(x_5);
x_1372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1372, 0, x_1370);
lean_ctor_set(x_1372, 1, x_1371);
lean_ctor_set(x_22, 0, x_1372);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_22);
x_16 = x_4;
goto block_21;
}
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_dec(x_22);
x_1373 = lean_ctor_get(x_5, 0);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_5, 1);
lean_inc(x_1374);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_1375 = x_5;
} else {
 lean_dec_ref(x_5);
 x_1375 = lean_box(0);
}
if (lean_is_scalar(x_1375)) {
 x_1376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1376 = x_1375;
}
lean_ctor_set(x_1376, 0, x_1373);
lean_ctor_set(x_1376, 1, x_1374);
x_1377 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1377, 0, x_1376);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_1377);
x_16 = x_4;
goto block_21;
}
}
case 2:
{
uint8_t x_1378; 
lean_free_object(x_4);
lean_dec(x_14);
x_1378 = !lean_is_exclusive(x_22);
if (x_1378 == 0)
{
lean_object* x_1379; lean_object* x_1380; uint8_t x_1381; 
x_1379 = lean_ctor_get(x_22, 1);
lean_dec(x_1379);
x_1380 = lean_ctor_get(x_22, 0);
lean_dec(x_1380);
x_1381 = !lean_is_exclusive(x_5);
if (x_1381 == 0)
{
lean_object* x_1382; 
x_1382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1382, 0, x_5);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 0, x_1382);
x_16 = x_22;
goto block_21;
}
else
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1383 = lean_ctor_get(x_5, 0);
x_1384 = lean_ctor_get(x_5, 1);
lean_inc(x_1384);
lean_inc(x_1383);
lean_dec(x_5);
x_1385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1385, 0, x_1383);
lean_ctor_set(x_1385, 1, x_1384);
x_1386 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1386, 0, x_1385);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 0, x_1386);
x_16 = x_22;
goto block_21;
}
}
else
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_22);
x_1387 = lean_ctor_get(x_5, 0);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_5, 1);
lean_inc(x_1388);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_1389 = x_5;
} else {
 lean_dec_ref(x_5);
 x_1389 = lean_box(0);
}
if (lean_is_scalar(x_1389)) {
 x_1390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1390 = x_1389;
}
lean_ctor_set(x_1390, 0, x_1387);
lean_ctor_set(x_1390, 1, x_1388);
x_1391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1391, 0, x_1390);
x_1392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1392, 0, x_1391);
lean_ctor_set(x_1392, 1, x_11);
x_16 = x_1392;
goto block_21;
}
}
default: 
{
uint8_t x_1393; 
lean_dec(x_14);
x_1393 = !lean_is_exclusive(x_22);
if (x_1393 == 0)
{
lean_object* x_1394; uint8_t x_1395; 
x_1394 = lean_ctor_get(x_22, 0);
lean_dec(x_1394);
x_1395 = !lean_is_exclusive(x_5);
if (x_1395 == 0)
{
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_22);
x_16 = x_4;
goto block_21;
}
else
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
x_1396 = lean_ctor_get(x_5, 0);
x_1397 = lean_ctor_get(x_5, 1);
lean_inc(x_1397);
lean_inc(x_1396);
lean_dec(x_5);
x_1398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1398, 0, x_1396);
lean_ctor_set(x_1398, 1, x_1397);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_1398);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_22);
x_16 = x_4;
goto block_21;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
lean_dec(x_22);
x_1399 = lean_ctor_get(x_5, 0);
lean_inc(x_1399);
x_1400 = lean_ctor_get(x_5, 1);
lean_inc(x_1400);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_1401 = x_5;
} else {
 lean_dec_ref(x_5);
 x_1401 = lean_box(0);
}
if (lean_is_scalar(x_1401)) {
 x_1402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1402 = x_1401;
}
lean_ctor_set(x_1402, 0, x_1399);
lean_ctor_set(x_1402, 1, x_1400);
x_1403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1403, 0, x_1402);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_1403);
x_16 = x_4;
goto block_21;
}
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_15;
x_5 = x_19;
x_6 = lean_box(0);
x_11 = x_18;
goto _start;
}
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1412; 
x_1404 = lean_ctor_get(x_4, 0);
x_1405 = lean_ctor_get(x_4, 1);
lean_inc(x_1405);
lean_inc(x_1404);
lean_dec(x_4);
x_1412 = lean_ctor_get(x_1404, 0);
lean_inc(x_1412);
switch (lean_obj_tag(x_1412)) {
case 0:
{
uint8_t x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; uint8_t x_1424; 
x_1413 = lean_ctor_get_uint8(x_1404, sizeof(void*)*1);
lean_dec(x_1404);
x_1414 = lean_ctor_get(x_5, 0);
lean_inc(x_1414);
x_1415 = lean_ctor_get(x_5, 1);
lean_inc(x_1415);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_1416 = x_5;
} else {
 lean_dec_ref(x_5);
 x_1416 = lean_box(0);
}
x_1417 = lean_ctor_get(x_1412, 0);
lean_inc(x_1417);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 x_1418 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1418 = lean_box(0);
}
x_1419 = lean_st_ref_get(x_10, x_11);
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1419, 1);
lean_inc(x_1421);
if (lean_is_exclusive(x_1419)) {
 lean_ctor_release(x_1419, 0);
 lean_ctor_release(x_1419, 1);
 x_1422 = x_1419;
} else {
 lean_dec_ref(x_1419);
 x_1422 = lean_box(0);
}
x_1423 = lean_ctor_get(x_1420, 0);
lean_inc(x_1423);
lean_dec(x_1420);
x_1424 = l_Lean_Meta_Match_isMatchEqnTheorem(x_1423, x_1417);
if (x_1424 == 0)
{
lean_object* x_1425; lean_object* x_1426; 
lean_dec(x_1422);
lean_dec(x_1418);
x_1425 = l_Lean_Meta_isEqnThm_x3f(x_1417, x_9, x_10, x_1421);
x_1426 = lean_ctor_get(x_1425, 0);
lean_inc(x_1426);
if (lean_obj_tag(x_1426) == 0)
{
lean_object* x_1427; uint8_t x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; 
lean_dec(x_1416);
x_1427 = lean_ctor_get(x_1425, 1);
lean_inc(x_1427);
lean_dec(x_1425);
x_1428 = 0;
lean_inc(x_9);
x_1429 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_1417, x_1428, x_7, x_8, x_9, x_10, x_1427);
x_1430 = lean_ctor_get(x_1429, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1429, 1);
lean_inc(x_1431);
if (lean_is_exclusive(x_1429)) {
 lean_ctor_release(x_1429, 0);
 lean_ctor_release(x_1429, 1);
 x_1432 = x_1429;
} else {
 lean_dec_ref(x_1429);
 x_1432 = lean_box(0);
}
x_1433 = lean_mk_syntax_ident(x_1430);
switch (x_1413) {
case 0:
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
lean_dec(x_1432);
x_1434 = lean_ctor_get(x_9, 5);
lean_inc(x_1434);
x_1435 = l_Lean_SourceInfo_fromRef(x_1434, x_1428);
lean_dec(x_1434);
x_1436 = lean_st_ref_get(x_10, x_1431);
x_1437 = lean_ctor_get(x_1436, 1);
lean_inc(x_1437);
if (lean_is_exclusive(x_1436)) {
 lean_ctor_release(x_1436, 0);
 lean_ctor_release(x_1436, 1);
 x_1438 = x_1436;
} else {
 lean_dec_ref(x_1436);
 x_1438 = lean_box(0);
}
x_1439 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1435);
if (lean_is_scalar(x_1438)) {
 x_1440 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1440 = x_1438;
 lean_ctor_set_tag(x_1440, 2);
}
lean_ctor_set(x_1440, 0, x_1435);
lean_ctor_set(x_1440, 1, x_1439);
x_1441 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2;
lean_inc(x_1435);
x_1442 = l_Lean_Syntax_node1(x_1435, x_1441, x_1440);
x_1443 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1435);
x_1444 = l_Lean_Syntax_node1(x_1435, x_1443, x_1442);
x_1445 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1435);
x_1446 = l_Lean_Syntax_node1(x_1435, x_1445, x_1444);
x_1447 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1435);
x_1448 = l_Lean_Syntax_node2(x_1435, x_1447, x_1446, x_1433);
x_1449 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1450 = l_Lean_Syntax_node1(x_1435, x_1449, x_1448);
x_1451 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1450, x_7, x_8, x_9, x_10, x_1437);
x_1406 = x_1451;
goto block_1411;
}
case 1:
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
x_1452 = lean_ctor_get(x_9, 5);
lean_inc(x_1452);
x_1453 = l_Lean_SourceInfo_fromRef(x_1452, x_1428);
lean_dec(x_1452);
x_1454 = lean_st_ref_get(x_10, x_1431);
x_1455 = lean_ctor_get(x_1454, 1);
lean_inc(x_1455);
if (lean_is_exclusive(x_1454)) {
 lean_ctor_release(x_1454, 0);
 lean_ctor_release(x_1454, 1);
 x_1456 = x_1454;
} else {
 lean_dec_ref(x_1454);
 x_1456 = lean_box(0);
}
x_1457 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1453);
if (lean_is_scalar(x_1456)) {
 x_1458 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1458 = x_1456;
 lean_ctor_set_tag(x_1458, 2);
}
lean_ctor_set(x_1458, 0, x_1453);
lean_ctor_set(x_1458, 1, x_1457);
x_1459 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_1453);
if (lean_is_scalar(x_1432)) {
 x_1460 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1460 = x_1432;
 lean_ctor_set_tag(x_1460, 2);
}
lean_ctor_set(x_1460, 0, x_1453);
lean_ctor_set(x_1460, 1, x_1459);
x_1461 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5;
lean_inc(x_1453);
x_1462 = l_Lean_Syntax_node2(x_1453, x_1461, x_1458, x_1460);
x_1463 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1453);
x_1464 = l_Lean_Syntax_node1(x_1453, x_1463, x_1462);
x_1465 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1453);
x_1466 = l_Lean_Syntax_node1(x_1453, x_1465, x_1464);
x_1467 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1453);
x_1468 = l_Lean_Syntax_node2(x_1453, x_1467, x_1466, x_1433);
x_1469 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1470 = l_Lean_Syntax_node1(x_1453, x_1469, x_1468);
x_1471 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1470, x_7, x_8, x_9, x_10, x_1455);
x_1406 = x_1471;
goto block_1411;
}
case 2:
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1472 = lean_ctor_get(x_9, 5);
lean_inc(x_1472);
x_1473 = l_Lean_SourceInfo_fromRef(x_1472, x_1428);
lean_dec(x_1472);
x_1474 = lean_st_ref_get(x_10, x_1431);
x_1475 = lean_ctor_get(x_1474, 1);
lean_inc(x_1475);
if (lean_is_exclusive(x_1474)) {
 lean_ctor_release(x_1474, 0);
 lean_ctor_release(x_1474, 1);
 x_1476 = x_1474;
} else {
 lean_dec_ref(x_1474);
 x_1476 = lean_box(0);
}
x_1477 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6;
lean_inc(x_1473);
if (lean_is_scalar(x_1476)) {
 x_1478 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1478 = x_1476;
 lean_ctor_set_tag(x_1478, 2);
}
lean_ctor_set(x_1478, 0, x_1473);
lean_ctor_set(x_1478, 1, x_1477);
x_1479 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1473);
if (lean_is_scalar(x_1432)) {
 x_1480 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1480 = x_1432;
 lean_ctor_set_tag(x_1480, 2);
}
lean_ctor_set(x_1480, 0, x_1473);
lean_ctor_set(x_1480, 1, x_1479);
x_1481 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8;
lean_inc(x_1478);
lean_inc(x_1473);
x_1482 = l_Lean_Syntax_node3(x_1473, x_1481, x_1478, x_1480, x_1478);
x_1483 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1473);
x_1484 = l_Lean_Syntax_node1(x_1473, x_1483, x_1482);
x_1485 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1473);
x_1486 = l_Lean_Syntax_node1(x_1473, x_1485, x_1484);
x_1487 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1473);
x_1488 = l_Lean_Syntax_node2(x_1473, x_1487, x_1486, x_1433);
x_1489 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1490 = l_Lean_Syntax_node1(x_1473, x_1489, x_1488);
x_1491 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1490, x_7, x_8, x_9, x_10, x_1475);
x_1406 = x_1491;
goto block_1411;
}
case 3:
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1492 = lean_ctor_get(x_9, 5);
lean_inc(x_1492);
x_1493 = l_Lean_SourceInfo_fromRef(x_1492, x_1428);
lean_dec(x_1492);
x_1494 = lean_st_ref_get(x_10, x_1431);
x_1495 = lean_ctor_get(x_1494, 1);
lean_inc(x_1495);
if (lean_is_exclusive(x_1494)) {
 lean_ctor_release(x_1494, 0);
 lean_ctor_release(x_1494, 1);
 x_1496 = x_1494;
} else {
 lean_dec_ref(x_1494);
 x_1496 = lean_box(0);
}
x_1497 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_1493);
if (lean_is_scalar(x_1496)) {
 x_1498 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1498 = x_1496;
 lean_ctor_set_tag(x_1498, 2);
}
lean_ctor_set(x_1498, 0, x_1493);
lean_ctor_set(x_1498, 1, x_1497);
x_1499 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3;
lean_inc(x_1493);
if (lean_is_scalar(x_1432)) {
 x_1500 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1500 = x_1432;
 lean_ctor_set_tag(x_1500, 2);
}
lean_ctor_set(x_1500, 0, x_1493);
lean_ctor_set(x_1500, 1, x_1499);
x_1501 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12;
lean_inc(x_1493);
x_1502 = l_Lean_Syntax_node2(x_1493, x_1501, x_1498, x_1500);
x_1503 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10;
lean_inc(x_1493);
x_1504 = l_Lean_Syntax_node1(x_1493, x_1503, x_1502);
x_1505 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1493);
x_1506 = l_Lean_Syntax_node1(x_1493, x_1505, x_1504);
x_1507 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1493);
x_1508 = l_Lean_Syntax_node1(x_1493, x_1507, x_1506);
x_1509 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1493);
x_1510 = l_Lean_Syntax_node2(x_1493, x_1509, x_1508, x_1433);
x_1511 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1512 = l_Lean_Syntax_node1(x_1493, x_1511, x_1510);
x_1513 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1512, x_7, x_8, x_9, x_10, x_1495);
x_1406 = x_1513;
goto block_1411;
}
case 4:
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; 
lean_dec(x_1432);
x_1514 = lean_ctor_get(x_9, 5);
lean_inc(x_1514);
x_1515 = l_Lean_SourceInfo_fromRef(x_1514, x_1428);
lean_dec(x_1514);
x_1516 = lean_st_ref_get(x_10, x_1431);
x_1517 = lean_ctor_get(x_1516, 1);
lean_inc(x_1517);
if (lean_is_exclusive(x_1516)) {
 lean_ctor_release(x_1516, 0);
 lean_ctor_release(x_1516, 1);
 x_1518 = x_1516;
} else {
 lean_dec_ref(x_1516);
 x_1518 = lean_box(0);
}
x_1519 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19;
lean_inc(x_1515);
if (lean_is_scalar(x_1518)) {
 x_1520 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1520 = x_1518;
 lean_ctor_set_tag(x_1520, 2);
}
lean_ctor_set(x_1520, 0, x_1515);
lean_ctor_set(x_1520, 1, x_1519);
x_1521 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18;
lean_inc(x_1515);
x_1522 = l_Lean_Syntax_node1(x_1515, x_1521, x_1520);
x_1523 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15;
lean_inc(x_1515);
x_1524 = l_Lean_Syntax_node1(x_1515, x_1523, x_1522);
x_1525 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1515);
x_1526 = l_Lean_Syntax_node1(x_1515, x_1525, x_1524);
x_1527 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1515);
x_1528 = l_Lean_Syntax_node1(x_1515, x_1527, x_1526);
x_1529 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1515);
x_1530 = l_Lean_Syntax_node2(x_1515, x_1529, x_1528, x_1433);
x_1531 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1532 = l_Lean_Syntax_node1(x_1515, x_1531, x_1530);
x_1533 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1532, x_7, x_8, x_9, x_10, x_1517);
x_1406 = x_1533;
goto block_1411;
}
case 5:
{
lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
lean_dec(x_1432);
x_1534 = lean_ctor_get(x_9, 5);
lean_inc(x_1534);
x_1535 = l_Lean_SourceInfo_fromRef(x_1534, x_1428);
lean_dec(x_1534);
x_1536 = lean_st_ref_get(x_10, x_1431);
x_1537 = lean_ctor_get(x_1536, 1);
lean_inc(x_1537);
if (lean_is_exclusive(x_1536)) {
 lean_ctor_release(x_1536, 0);
 lean_ctor_release(x_1536, 1);
 x_1538 = x_1536;
} else {
 lean_dec_ref(x_1536);
 x_1538 = lean_box(0);
}
x_1539 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13;
lean_inc(x_1535);
if (lean_is_scalar(x_1538)) {
 x_1540 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1540 = x_1538;
 lean_ctor_set_tag(x_1540, 2);
}
lean_ctor_set(x_1540, 0, x_1535);
lean_ctor_set(x_1540, 1, x_1539);
x_1541 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23;
lean_inc(x_1535);
x_1542 = l_Lean_Syntax_node1(x_1535, x_1541, x_1540);
x_1543 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21;
lean_inc(x_1535);
x_1544 = l_Lean_Syntax_node1(x_1535, x_1543, x_1542);
x_1545 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1535);
x_1546 = l_Lean_Syntax_node1(x_1535, x_1545, x_1544);
x_1547 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1535);
x_1548 = l_Lean_Syntax_node1(x_1535, x_1547, x_1546);
x_1549 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1535);
x_1550 = l_Lean_Syntax_node2(x_1535, x_1549, x_1548, x_1433);
x_1551 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1552 = l_Lean_Syntax_node1(x_1535, x_1551, x_1550);
x_1553 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1552, x_7, x_8, x_9, x_10, x_1537);
x_1406 = x_1553;
goto block_1411;
}
case 6:
{
lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
lean_dec(x_1432);
x_1554 = lean_ctor_get(x_9, 5);
lean_inc(x_1554);
x_1555 = l_Lean_SourceInfo_fromRef(x_1554, x_1428);
lean_dec(x_1554);
x_1556 = lean_st_ref_get(x_10, x_1431);
x_1557 = lean_ctor_get(x_1556, 1);
lean_inc(x_1557);
if (lean_is_exclusive(x_1556)) {
 lean_ctor_release(x_1556, 0);
 lean_ctor_release(x_1556, 1);
 x_1558 = x_1556;
} else {
 lean_dec_ref(x_1556);
 x_1558 = lean_box(0);
}
x_1559 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28;
lean_inc(x_1555);
if (lean_is_scalar(x_1558)) {
 x_1560 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1560 = x_1558;
 lean_ctor_set_tag(x_1560, 2);
}
lean_ctor_set(x_1560, 0, x_1555);
lean_ctor_set(x_1560, 1, x_1559);
x_1561 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27;
lean_inc(x_1555);
x_1562 = l_Lean_Syntax_node1(x_1555, x_1561, x_1560);
x_1563 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25;
lean_inc(x_1555);
x_1564 = l_Lean_Syntax_node1(x_1555, x_1563, x_1562);
x_1565 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1555);
x_1566 = l_Lean_Syntax_node1(x_1555, x_1565, x_1564);
x_1567 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1555);
x_1568 = l_Lean_Syntax_node1(x_1555, x_1567, x_1566);
x_1569 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1555);
x_1570 = l_Lean_Syntax_node2(x_1555, x_1569, x_1568, x_1433);
x_1571 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1572 = l_Lean_Syntax_node1(x_1555, x_1571, x_1570);
x_1573 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1572, x_7, x_8, x_9, x_10, x_1557);
x_1406 = x_1573;
goto block_1411;
}
case 7:
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; 
lean_dec(x_1432);
x_1574 = lean_ctor_get(x_9, 5);
lean_inc(x_1574);
x_1575 = l_Lean_SourceInfo_fromRef(x_1574, x_1428);
lean_dec(x_1574);
x_1576 = lean_st_ref_get(x_10, x_1431);
x_1577 = lean_ctor_get(x_1576, 1);
lean_inc(x_1577);
if (lean_is_exclusive(x_1576)) {
 lean_ctor_release(x_1576, 0);
 lean_ctor_release(x_1576, 1);
 x_1578 = x_1576;
} else {
 lean_dec_ref(x_1576);
 x_1578 = lean_box(0);
}
x_1579 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33;
lean_inc(x_1575);
if (lean_is_scalar(x_1578)) {
 x_1580 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1580 = x_1578;
 lean_ctor_set_tag(x_1580, 2);
}
lean_ctor_set(x_1580, 0, x_1575);
lean_ctor_set(x_1580, 1, x_1579);
x_1581 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32;
lean_inc(x_1575);
x_1582 = l_Lean_Syntax_node1(x_1575, x_1581, x_1580);
x_1583 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30;
lean_inc(x_1575);
x_1584 = l_Lean_Syntax_node1(x_1575, x_1583, x_1582);
x_1585 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1575);
x_1586 = l_Lean_Syntax_node1(x_1575, x_1585, x_1584);
x_1587 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1575);
x_1588 = l_Lean_Syntax_node1(x_1575, x_1587, x_1586);
x_1589 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1575);
x_1590 = l_Lean_Syntax_node2(x_1575, x_1589, x_1588, x_1433);
x_1591 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1592 = l_Lean_Syntax_node1(x_1575, x_1591, x_1590);
x_1593 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1592, x_7, x_8, x_9, x_10, x_1577);
x_1406 = x_1593;
goto block_1411;
}
case 8:
{
lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
lean_dec(x_1432);
x_1594 = lean_ctor_get(x_9, 5);
lean_inc(x_1594);
x_1595 = l_Lean_SourceInfo_fromRef(x_1594, x_1428);
lean_dec(x_1594);
x_1596 = lean_st_ref_get(x_10, x_1431);
x_1597 = lean_ctor_get(x_1596, 1);
lean_inc(x_1597);
lean_dec(x_1596);
x_1598 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_1599 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_1595);
x_1600 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1600, 0, x_1595);
lean_ctor_set(x_1600, 1, x_1598);
lean_ctor_set(x_1600, 2, x_1599);
x_1601 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1595);
x_1602 = l_Lean_Syntax_node2(x_1595, x_1601, x_1600, x_1433);
x_1603 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1604 = l_Lean_Syntax_node1(x_1595, x_1603, x_1602);
x_1605 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1604, x_7, x_8, x_9, x_10, x_1597);
x_1406 = x_1605;
goto block_1411;
}
default: 
{
lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; 
lean_dec(x_1432);
x_1606 = lean_ctor_get(x_9, 5);
lean_inc(x_1606);
x_1607 = l_Lean_SourceInfo_fromRef(x_1606, x_1428);
lean_dec(x_1606);
x_1608 = lean_st_ref_get(x_10, x_1431);
x_1609 = lean_ctor_get(x_1608, 1);
lean_inc(x_1609);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1610 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1610 = lean_box(0);
}
x_1611 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36;
lean_inc(x_1607);
if (lean_is_scalar(x_1610)) {
 x_1612 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1612 = x_1610;
 lean_ctor_set_tag(x_1612, 2);
}
lean_ctor_set(x_1612, 0, x_1607);
lean_ctor_set(x_1612, 1, x_1611);
x_1613 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35;
lean_inc(x_1607);
x_1614 = l_Lean_Syntax_node1(x_1607, x_1613, x_1612);
x_1615 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_1607);
x_1616 = l_Lean_Syntax_node1(x_1607, x_1615, x_1614);
x_1617 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_1607);
x_1618 = l_Lean_Syntax_node1(x_1607, x_1617, x_1616);
x_1619 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1607);
x_1620 = l_Lean_Syntax_node2(x_1607, x_1619, x_1618, x_1433);
x_1621 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1622 = l_Lean_Syntax_node1(x_1607, x_1621, x_1620);
x_1623 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1414, x_1415, x_1622, x_7, x_8, x_9, x_10, x_1609);
x_1406 = x_1623;
goto block_1411;
}
}
}
else
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; uint8_t x_1628; 
lean_dec(x_1417);
x_1624 = lean_ctor_get(x_1425, 1);
lean_inc(x_1624);
if (lean_is_exclusive(x_1425)) {
 lean_ctor_release(x_1425, 0);
 lean_ctor_release(x_1425, 1);
 x_1625 = x_1425;
} else {
 lean_dec_ref(x_1425);
 x_1625 = lean_box(0);
}
x_1626 = lean_ctor_get(x_1426, 0);
lean_inc(x_1626);
if (lean_is_exclusive(x_1426)) {
 lean_ctor_release(x_1426, 0);
 x_1627 = x_1426;
} else {
 lean_dec_ref(x_1426);
 x_1627 = lean_box(0);
}
x_1628 = l_Lean_NameSet_contains(x_1414, x_1626);
if (x_1628 == 0)
{
lean_object* x_1629; lean_object* x_1630; uint8_t x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; 
lean_dec(x_1625);
x_1629 = lean_box(0);
lean_inc(x_1626);
x_1630 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1414, x_1626, x_1629);
x_1631 = 0;
lean_inc(x_9);
x_1632 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_1626, x_1631, x_7, x_8, x_9, x_10, x_1624);
x_1633 = lean_ctor_get(x_1632, 0);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1632, 1);
lean_inc(x_1634);
lean_dec(x_1632);
x_1635 = lean_mk_syntax_ident(x_1633);
x_1636 = lean_ctor_get(x_9, 5);
lean_inc(x_1636);
x_1637 = l_Lean_SourceInfo_fromRef(x_1636, x_1631);
lean_dec(x_1636);
x_1638 = lean_st_ref_get(x_10, x_1634);
x_1639 = lean_ctor_get(x_1638, 1);
lean_inc(x_1639);
if (lean_is_exclusive(x_1638)) {
 lean_ctor_release(x_1638, 0);
 lean_ctor_release(x_1638, 1);
 x_1640 = x_1638;
} else {
 lean_dec_ref(x_1638);
 x_1640 = lean_box(0);
}
x_1641 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
x_1642 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_1637);
x_1643 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1643, 0, x_1637);
lean_ctor_set(x_1643, 1, x_1641);
lean_ctor_set(x_1643, 2, x_1642);
x_1644 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_1637);
x_1645 = l_Lean_Syntax_node2(x_1637, x_1644, x_1643, x_1635);
x_1646 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_1647 = l_Lean_Syntax_node1(x_1637, x_1646, x_1645);
x_1648 = lean_array_push(x_1415, x_1647);
if (lean_is_scalar(x_1416)) {
 x_1649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1649 = x_1416;
}
lean_ctor_set(x_1649, 0, x_1630);
lean_ctor_set(x_1649, 1, x_1648);
if (lean_is_scalar(x_1627)) {
 x_1650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1650 = x_1627;
}
lean_ctor_set(x_1650, 0, x_1649);
if (lean_is_scalar(x_1640)) {
 x_1651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1651 = x_1640;
}
lean_ctor_set(x_1651, 0, x_1650);
lean_ctor_set(x_1651, 1, x_1639);
x_1406 = x_1651;
goto block_1411;
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
lean_dec(x_1626);
if (lean_is_scalar(x_1416)) {
 x_1652 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1652 = x_1416;
}
lean_ctor_set(x_1652, 0, x_1414);
lean_ctor_set(x_1652, 1, x_1415);
if (lean_is_scalar(x_1627)) {
 x_1653 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1653 = x_1627;
}
lean_ctor_set(x_1653, 0, x_1652);
if (lean_is_scalar(x_1625)) {
 x_1654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1654 = x_1625;
}
lean_ctor_set(x_1654, 0, x_1653);
lean_ctor_set(x_1654, 1, x_1624);
x_1406 = x_1654;
goto block_1411;
}
}
}
else
{
lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
lean_dec(x_1417);
if (lean_is_scalar(x_1416)) {
 x_1655 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1655 = x_1416;
}
lean_ctor_set(x_1655, 0, x_1414);
lean_ctor_set(x_1655, 1, x_1415);
if (lean_is_scalar(x_1418)) {
 x_1656 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1656 = x_1418;
 lean_ctor_set_tag(x_1656, 1);
}
lean_ctor_set(x_1656, 0, x_1655);
if (lean_is_scalar(x_1422)) {
 x_1657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1657 = x_1422;
}
lean_ctor_set(x_1657, 0, x_1656);
lean_ctor_set(x_1657, 1, x_1421);
x_1406 = x_1657;
goto block_1411;
}
}
case 1:
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; 
lean_dec(x_1404);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 x_1658 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1658 = lean_box(0);
}
x_1659 = lean_ctor_get(x_5, 0);
lean_inc(x_1659);
x_1660 = lean_ctor_get(x_5, 1);
lean_inc(x_1660);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_1661 = x_5;
} else {
 lean_dec_ref(x_5);
 x_1661 = lean_box(0);
}
if (lean_is_scalar(x_1661)) {
 x_1662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1662 = x_1661;
}
lean_ctor_set(x_1662, 0, x_1659);
lean_ctor_set(x_1662, 1, x_1660);
if (lean_is_scalar(x_1658)) {
 x_1663 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1663 = x_1658;
}
lean_ctor_set(x_1663, 0, x_1662);
x_1664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1664, 0, x_1663);
lean_ctor_set(x_1664, 1, x_11);
x_1406 = x_1664;
goto block_1411;
}
case 2:
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; 
lean_dec(x_1404);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 lean_ctor_release(x_1412, 1);
 x_1665 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1665 = lean_box(0);
}
x_1666 = lean_ctor_get(x_5, 0);
lean_inc(x_1666);
x_1667 = lean_ctor_get(x_5, 1);
lean_inc(x_1667);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_1668 = x_5;
} else {
 lean_dec_ref(x_5);
 x_1668 = lean_box(0);
}
if (lean_is_scalar(x_1668)) {
 x_1669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1669 = x_1668;
}
lean_ctor_set(x_1669, 0, x_1666);
lean_ctor_set(x_1669, 1, x_1667);
x_1670 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1670, 0, x_1669);
if (lean_is_scalar(x_1665)) {
 x_1671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1671 = x_1665;
 lean_ctor_set_tag(x_1671, 0);
}
lean_ctor_set(x_1671, 0, x_1670);
lean_ctor_set(x_1671, 1, x_11);
x_1406 = x_1671;
goto block_1411;
}
default: 
{
lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
lean_dec(x_1404);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 x_1672 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1672 = lean_box(0);
}
x_1673 = lean_ctor_get(x_5, 0);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_5, 1);
lean_inc(x_1674);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_1675 = x_5;
} else {
 lean_dec_ref(x_5);
 x_1675 = lean_box(0);
}
if (lean_is_scalar(x_1675)) {
 x_1676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1676 = x_1675;
}
lean_ctor_set(x_1676, 0, x_1673);
lean_ctor_set(x_1676, 1, x_1674);
if (lean_is_scalar(x_1672)) {
 x_1677 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1677 = x_1672;
 lean_ctor_set_tag(x_1677, 1);
}
lean_ctor_set(x_1677, 0, x_1676);
x_1678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1678, 0, x_1677);
lean_ctor_set(x_1678, 1, x_11);
x_1406 = x_1678;
goto block_1411;
}
}
block_1411:
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
x_1407 = lean_ctor_get(x_1406, 0);
lean_inc(x_1407);
x_1408 = lean_ctor_get(x_1406, 1);
lean_inc(x_1408);
lean_dec(x_1406);
x_1409 = lean_ctor_get(x_1407, 0);
lean_inc(x_1409);
lean_dec(x_1407);
x_4 = x_1405;
x_5 = x_1409;
x_6 = lean_box(0);
x_11 = x_1408;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___closed__1;
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__13(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__15(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindCasesEager", 15, 15);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cases", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eager", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
x_16 = l_Lean_NameSet_contains(x_15, x_13);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_17 = 0;
lean_inc(x_9);
x_18 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_13, x_17, x_7, x_8, x_9, x_10, x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_mk_syntax_ident(x_20);
x_23 = lean_ctor_get(x_9, 5);
lean_inc(x_23);
x_24 = l_Lean_SourceInfo_fromRef(x_23, x_17);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_10, x_21);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3;
lean_inc(x_24);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_29);
lean_ctor_set(x_25, 0, x_24);
x_30 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4;
lean_inc(x_24);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_24);
x_31 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2;
lean_inc(x_24);
x_32 = l_Lean_Syntax_node2(x_24, x_31, x_25, x_18);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_24);
x_34 = l_Lean_Syntax_node1(x_24, x_33, x_32);
x_35 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_24);
x_36 = l_Lean_Syntax_node1(x_24, x_35, x_34);
x_37 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_24);
x_38 = l_Lean_Syntax_node2(x_24, x_37, x_36, x_22);
x_39 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_40 = l_Lean_Syntax_node1(x_24, x_39, x_38);
x_41 = lean_array_push(x_5, x_40);
x_4 = x_14;
x_5 = x_41;
x_6 = lean_box(0);
x_11 = x_27;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3;
lean_inc(x_24);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_24);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4;
lean_inc(x_24);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_46);
lean_ctor_set(x_18, 0, x_24);
x_47 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2;
lean_inc(x_24);
x_48 = l_Lean_Syntax_node2(x_24, x_47, x_45, x_18);
x_49 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_24);
x_50 = l_Lean_Syntax_node1(x_24, x_49, x_48);
x_51 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_24);
x_52 = l_Lean_Syntax_node1(x_24, x_51, x_50);
x_53 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_24);
x_54 = l_Lean_Syntax_node2(x_24, x_53, x_52, x_22);
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_56 = l_Lean_Syntax_node1(x_24, x_55, x_54);
x_57 = lean_array_push(x_5, x_56);
x_4 = x_14;
x_5 = x_57;
x_6 = lean_box(0);
x_11 = x_43;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_mk_syntax_ident(x_59);
x_62 = lean_ctor_get(x_9, 5);
lean_inc(x_62);
x_63 = l_Lean_SourceInfo_fromRef(x_62, x_17);
lean_dec(x_62);
x_64 = lean_st_ref_get(x_10, x_60);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3;
lean_inc(x_63);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(2, 2, 0);
} else {
 x_68 = x_66;
 lean_ctor_set_tag(x_68, 2);
}
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4;
lean_inc(x_63);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2;
lean_inc(x_63);
x_72 = l_Lean_Syntax_node2(x_63, x_71, x_68, x_70);
x_73 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_63);
x_74 = l_Lean_Syntax_node1(x_63, x_73, x_72);
x_75 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_63);
x_76 = l_Lean_Syntax_node1(x_63, x_75, x_74);
x_77 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_63);
x_78 = l_Lean_Syntax_node2(x_63, x_77, x_76, x_61);
x_79 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_80 = l_Lean_Syntax_node1(x_63, x_79, x_78);
x_81 = lean_array_push(x_5, x_80);
x_4 = x_14;
x_5 = x_81;
x_6 = lean_box(0);
x_11 = x_65;
goto _start;
}
}
else
{
lean_dec(x_13);
x_4 = x_14;
x_6 = lean_box(0);
goto _start;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindCases", 10, 10);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7;
x_4 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
lean_inc(x_1);
x_16 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_1, x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
x_18 = l_Lean_NameSet_contains(x_17, x_14);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = 0;
lean_inc(x_10);
x_20 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_14, x_19, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_mk_syntax_ident(x_21);
x_24 = lean_ctor_get(x_10, 5);
lean_inc(x_24);
x_25 = l_Lean_SourceInfo_fromRef(x_24, x_19);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_11, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3;
lean_inc(x_25);
lean_ctor_set_tag(x_26, 2);
lean_ctor_set(x_26, 1, x_30);
lean_ctor_set(x_26, 0, x_25);
x_31 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__2;
lean_inc(x_25);
x_32 = l_Lean_Syntax_node1(x_25, x_31, x_26);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_25);
x_34 = l_Lean_Syntax_node1(x_25, x_33, x_32);
x_35 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_25);
x_36 = l_Lean_Syntax_node1(x_25, x_35, x_34);
x_37 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_25);
x_38 = l_Lean_Syntax_node2(x_25, x_37, x_36, x_23);
x_39 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_40 = l_Lean_Syntax_node1(x_25, x_39, x_38);
x_41 = lean_array_push(x_6, x_40);
x_5 = x_15;
x_6 = x_41;
x_7 = lean_box(0);
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_dec(x_26);
x_44 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3;
lean_inc(x_25);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__2;
lean_inc(x_25);
x_47 = l_Lean_Syntax_node1(x_25, x_46, x_45);
x_48 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9;
lean_inc(x_25);
x_49 = l_Lean_Syntax_node1(x_25, x_48, x_47);
x_50 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_25);
x_51 = l_Lean_Syntax_node1(x_25, x_50, x_49);
x_52 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6;
lean_inc(x_25);
x_53 = l_Lean_Syntax_node2(x_25, x_52, x_51, x_23);
x_54 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2;
x_55 = l_Lean_Syntax_node1(x_25, x_54, x_53);
x_56 = lean_array_push(x_6, x_55);
x_5 = x_15;
x_6 = x_56;
x_7 = lean_box(0);
x_12 = x_43;
goto _start;
}
}
else
{
lean_dec(x_14);
x_5 = x_15;
x_7 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_14);
x_5 = x_15;
x_7 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_Tactic_setGrindParams(x_2, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkGrindOnly___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkGrindOnly___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_mkGrindOnly___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("on_failure", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__1(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Tactic_mkGrindOnly___closed__1;
lean_inc(x_6);
lean_inc(x_10);
x_13 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11(x_10, x_11, x_10, x_10, x_12, lean_box(0), x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12(x_17);
lean_inc(x_6);
lean_inc(x_18);
x_19 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16(x_18, x_11, x_18, x_18, x_16, lean_box(0), x_4, x_5, x_6, x_7, x_15);
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_3, 2);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12(x_23);
lean_dec(x_23);
lean_inc(x_6);
lean_inc(x_24);
x_25 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17(x_17, x_11, x_24, x_24, x_24, x_21, lean_box(0), x_4, x_5, x_6, x_7, x_22);
lean_dec(x_24);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_26; 
lean_free_object(x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_6, 5);
lean_inc(x_29);
x_30 = 0;
x_31 = l_Lean_SourceInfo_fromRef(x_29, x_30);
lean_dec(x_29);
x_32 = lean_st_ref_get(x_7, x_28);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_31);
lean_ctor_set_tag(x_32, 2);
lean_ctor_set(x_32, 1, x_36);
lean_ctor_set(x_32, 0, x_31);
x_37 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_31);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_37);
lean_ctor_set(x_25, 0, x_31);
x_38 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_31);
x_39 = l_Lean_Syntax_node1(x_31, x_38, x_25);
x_40 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_31);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
lean_inc(x_41);
x_43 = l_Lean_Syntax_node5(x_31, x_42, x_32, x_1, x_39, x_41, x_41);
x_44 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_27, x_43, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_6);
lean_dec(x_27);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
x_46 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_31);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_31);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_48);
lean_ctor_set(x_25, 0, x_31);
x_49 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_31);
x_50 = l_Lean_Syntax_node1(x_31, x_49, x_25);
x_51 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_31);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_49);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
lean_inc(x_52);
x_54 = l_Lean_Syntax_node5(x_31, x_53, x_47, x_1, x_50, x_52, x_52);
x_55 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_27, x_54, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_6);
lean_dec(x_27);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_56 = lean_ctor_get(x_25, 0);
x_57 = lean_ctor_get(x_25, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_25);
x_58 = lean_ctor_get(x_6, 5);
lean_inc(x_58);
x_59 = 0;
x_60 = l_Lean_SourceInfo_fromRef(x_58, x_59);
lean_dec(x_58);
x_61 = lean_st_ref_get(x_7, x_57);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_60);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(2, 2, 0);
} else {
 x_65 = x_63;
 lean_ctor_set_tag(x_65, 2);
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_60);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_60);
x_69 = l_Lean_Syntax_node1(x_60, x_68, x_67);
x_70 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_60);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_71, 2, x_70);
x_72 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
lean_inc(x_71);
x_73 = l_Lean_Syntax_node5(x_60, x_72, x_65, x_1, x_69, x_71, x_71);
x_74 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_56, x_73, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_6);
lean_dec(x_56);
return x_74;
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_25);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_76 = lean_ctor_get(x_25, 0);
x_77 = lean_ctor_get(x_25, 1);
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
lean_dec(x_2);
x_79 = lean_ctor_get(x_6, 5);
lean_inc(x_79);
x_80 = 0;
x_81 = l_Lean_SourceInfo_fromRef(x_79, x_80);
lean_dec(x_79);
x_82 = lean_st_ref_get(x_7, x_77);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_82, 1);
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
x_86 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_81);
lean_ctor_set_tag(x_82, 2);
lean_ctor_set(x_82, 1, x_86);
lean_ctor_set(x_82, 0, x_81);
x_87 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_81);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_87);
lean_ctor_set(x_25, 0, x_81);
x_88 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_81);
x_89 = l_Lean_Syntax_node1(x_81, x_88, x_25);
x_90 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_81);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_81);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_91, 2, x_90);
x_92 = l_Lean_Elab_Tactic_mkGrindOnly___closed__3;
lean_inc(x_81);
lean_ctor_set_tag(x_19, 2);
lean_ctor_set(x_19, 1, x_92);
lean_ctor_set(x_19, 0, x_81);
lean_inc(x_81);
x_93 = l_Lean_Syntax_node2(x_81, x_88, x_19, x_78);
x_94 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
x_95 = l_Lean_Syntax_node5(x_81, x_94, x_82, x_1, x_89, x_91, x_93);
x_96 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_76, x_95, x_4, x_5, x_6, x_7, x_84);
lean_dec(x_6);
lean_dec(x_76);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_81);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_81);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_81);
lean_ctor_set_tag(x_25, 2);
lean_ctor_set(x_25, 1, x_100);
lean_ctor_set(x_25, 0, x_81);
x_101 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_81);
x_102 = l_Lean_Syntax_node1(x_81, x_101, x_25);
x_103 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_81);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_81);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_103);
x_105 = l_Lean_Elab_Tactic_mkGrindOnly___closed__3;
lean_inc(x_81);
lean_ctor_set_tag(x_19, 2);
lean_ctor_set(x_19, 1, x_105);
lean_ctor_set(x_19, 0, x_81);
lean_inc(x_81);
x_106 = l_Lean_Syntax_node2(x_81, x_101, x_19, x_78);
x_107 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
x_108 = l_Lean_Syntax_node5(x_81, x_107, x_99, x_1, x_102, x_104, x_106);
x_109 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_76, x_108, x_4, x_5, x_6, x_7, x_97);
lean_dec(x_6);
lean_dec(x_76);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_110 = lean_ctor_get(x_25, 0);
x_111 = lean_ctor_get(x_25, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_25);
x_112 = lean_ctor_get(x_2, 0);
lean_inc(x_112);
lean_dec(x_2);
x_113 = lean_ctor_get(x_6, 5);
lean_inc(x_113);
x_114 = 0;
x_115 = l_Lean_SourceInfo_fromRef(x_113, x_114);
lean_dec(x_113);
x_116 = lean_st_ref_get(x_7, x_111);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_115);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(2, 2, 0);
} else {
 x_120 = x_118;
 lean_ctor_set_tag(x_120, 2);
}
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_115);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_115);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_115);
x_124 = l_Lean_Syntax_node1(x_115, x_123, x_122);
x_125 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_115);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_115);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_125);
x_127 = l_Lean_Elab_Tactic_mkGrindOnly___closed__3;
lean_inc(x_115);
lean_ctor_set_tag(x_19, 2);
lean_ctor_set(x_19, 1, x_127);
lean_ctor_set(x_19, 0, x_115);
lean_inc(x_115);
x_128 = l_Lean_Syntax_node2(x_115, x_123, x_19, x_112);
x_129 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
x_130 = l_Lean_Syntax_node5(x_115, x_129, x_120, x_1, x_124, x_126, x_128);
x_131 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_110, x_130, x_4, x_5, x_6, x_7, x_117);
lean_dec(x_6);
lean_dec(x_110);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_19, 0);
x_133 = lean_ctor_get(x_19, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_19);
x_134 = lean_ctor_get(x_3, 2);
lean_inc(x_134);
lean_dec(x_3);
x_135 = l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12(x_134);
lean_dec(x_134);
lean_inc(x_6);
lean_inc(x_135);
x_136 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17(x_17, x_11, x_135, x_135, x_135, x_132, lean_box(0), x_4, x_5, x_6, x_7, x_133);
lean_dec(x_135);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_6, 5);
lean_inc(x_140);
x_141 = 0;
x_142 = l_Lean_SourceInfo_fromRef(x_140, x_141);
lean_dec(x_140);
x_143 = lean_st_ref_get(x_7, x_138);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_142);
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(2, 2, 0);
} else {
 x_147 = x_145;
 lean_ctor_set_tag(x_147, 2);
}
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_142);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(2, 2, 0);
} else {
 x_149 = x_139;
 lean_ctor_set_tag(x_149, 2);
}
lean_ctor_set(x_149, 0, x_142);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_142);
x_151 = l_Lean_Syntax_node1(x_142, x_150, x_149);
x_152 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_142);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_142);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_152);
x_154 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
lean_inc(x_153);
x_155 = l_Lean_Syntax_node5(x_142, x_154, x_147, x_1, x_151, x_153, x_153);
x_156 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_137, x_155, x_4, x_5, x_6, x_7, x_144);
lean_dec(x_6);
lean_dec(x_137);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_157 = lean_ctor_get(x_136, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_136, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_159 = x_136;
} else {
 lean_dec_ref(x_136);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_2, 0);
lean_inc(x_160);
lean_dec(x_2);
x_161 = lean_ctor_get(x_6, 5);
lean_inc(x_161);
x_162 = 0;
x_163 = l_Lean_SourceInfo_fromRef(x_161, x_162);
lean_dec(x_161);
x_164 = lean_st_ref_get(x_7, x_158);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
x_167 = l_Lean_Elab_Tactic_isGrindOnly___closed__1;
lean_inc(x_163);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(2, 2, 0);
} else {
 x_168 = x_166;
 lean_ctor_set_tag(x_168, 2);
}
lean_ctor_set(x_168, 0, x_163);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_Elab_Tactic_mkGrindOnly___closed__2;
lean_inc(x_163);
if (lean_is_scalar(x_159)) {
 x_170 = lean_alloc_ctor(2, 2, 0);
} else {
 x_170 = x_159;
 lean_ctor_set_tag(x_170, 2);
}
lean_ctor_set(x_170, 0, x_163);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Elab_Tactic_setGrindParams___closed__9;
lean_inc(x_163);
x_172 = l_Lean_Syntax_node1(x_163, x_171, x_170);
x_173 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
lean_inc(x_163);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_163);
lean_ctor_set(x_174, 1, x_171);
lean_ctor_set(x_174, 2, x_173);
x_175 = l_Lean_Elab_Tactic_mkGrindOnly___closed__3;
lean_inc(x_163);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_163);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_163);
x_177 = l_Lean_Syntax_node2(x_163, x_171, x_176, x_160);
x_178 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
x_179 = l_Lean_Syntax_node5(x_163, x_178, x_168, x_1, x_172, x_174, x_177);
x_180 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_157, x_179, x_4, x_5, x_6, x_7, x_165);
lean_dec(x_6);
lean_dec(x_157);
return x_180;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__9(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_mkGrindOnly___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_mkGrindOnly___spec__10(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__3(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_Elab_Tactic_mkGrindOnly___spec__14(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__13___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__13(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PersistentHashSet_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__12(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_mkGrindOnly___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindOnly___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_mkGrindOnly(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg), 1, 0);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Lean_Elab_Tactic_elabGrindConfig(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_evalGrindCore(x_2, x_17, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(2u);
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
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_16, x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_evalGrind___lambda__1(x_2, x_1, x_3, x_5, x_24, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_evalGrind___lambda__1(x_2, x_1, x_3, x_5, x_27, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_inc(x_15);
x_17 = l_Lean_Syntax_matchesNull(x_15, x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
lean_dec(x_15);
x_21 = l_Lean_Syntax_getArgs(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_Tactic_evalGrind___lambda__2(x_1, x_2, x_4, x_23, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Tactic_evalGrind___lambda__2(x_1, x_2, x_4, x_26, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Lean_Elab_Tactic_evalGrind___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_evalGrind___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
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
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
x_21 = l_Lean_Syntax_isNone(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_inc(x_20);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_14);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
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
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_20, x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_evalGrind___lambda__3(x_1, x_15, x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_26);
lean_dec(x_1);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_20);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Tactic_evalGrind___lambda__3(x_1, x_15, x_30, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_evalGrind___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalGrind___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalGrind___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalGrind", 9, 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3;
x_3 = l_Lean_Elab_Tactic_isGrindOnly___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Lean_Elab_Tactic_elabGrindConfig(x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 1;
lean_ctor_set_uint8(x_18, sizeof(void*)*6, x_21);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
x_22 = l_Lean_Elab_Tactic_evalGrindCore(x_2, x_18, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_14);
x_25 = l_Lean_Elab_Tactic_mkGrindOnly(x_1, x_7, x_23, x_12, x_13, x_14, x_15, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_14, 5);
lean_inc(x_29);
x_30 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2;
lean_ctor_set(x_25, 1, x_27);
lean_ctor_set(x_25, 0, x_30);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_29);
x_34 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3;
x_35 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_5, x_32, x_33, x_34, x_31, x_12, x_13, x_14, x_15, x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_38 = lean_ctor_get(x_14, 5);
lean_inc(x_38);
x_39 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_41);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set(x_42, 5, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_44 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3;
x_45 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_5, x_42, x_43, x_44, x_41, x_12, x_13, x_14, x_15, x_37);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
x_52 = lean_ctor_get(x_18, 2);
x_53 = lean_ctor_get(x_18, 3);
x_54 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 1);
x_55 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 2);
x_56 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 3);
x_57 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 4);
x_58 = lean_ctor_get(x_18, 4);
x_59 = lean_ctor_get(x_18, 5);
x_60 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 5);
x_61 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 6);
x_62 = lean_ctor_get_uint8(x_18, sizeof(void*)*6 + 7);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_63 = 1;
x_64 = lean_alloc_ctor(0, 6, 8);
lean_ctor_set(x_64, 0, x_50);
lean_ctor_set(x_64, 1, x_51);
lean_ctor_set(x_64, 2, x_52);
lean_ctor_set(x_64, 3, x_53);
lean_ctor_set(x_64, 4, x_58);
lean_ctor_set(x_64, 5, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 1, x_54);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 2, x_55);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 3, x_56);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 4, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 5, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 6, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 7, x_62);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_7);
x_65 = l_Lean_Elab_Tactic_evalGrindCore(x_2, x_64, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_14);
x_68 = l_Lean_Elab_Tactic_mkGrindOnly(x_1, x_7, x_66, x_12, x_13, x_14, x_15, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_14, 5);
lean_inc(x_72);
x_73 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2;
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_75);
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 5, x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_78 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3;
x_79 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_5, x_76, x_77, x_78, x_75, x_12, x_13, x_14, x_15, x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_1);
x_80 = lean_ctor_get(x_65, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_82 = x_65;
} else {
 lean_dec_ref(x_65);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_17);
if (x_84 == 0)
{
return x_17;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_17, 0);
x_86 = lean_ctor_get(x_17, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_17);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(4u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(2u);
lean_inc(x_17);
x_20 = l_Lean_Syntax_matchesNull(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_17, x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1(x_2, x_1, x_3, x_6, x_4, x_25, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_17);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1(x_2, x_1, x_3, x_6, x_4, x_28, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_inc(x_16);
x_18 = l_Lean_Syntax_matchesNull(x_16, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_19 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_16, x_20);
lean_dec(x_16);
x_22 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__2(x_1, x_2, x_5, x_3, x_24, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__2(x_1, x_2, x_5, x_3, x_27, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindTrace", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrindTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Lean_Elab_Tactic_evalGrindTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalGrindTrace___closed__2;
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
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Elab_Tactic_evalGrind___closed__2;
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
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
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_1, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_inc(x_22);
x_24 = l_Lean_Syntax_matchesNull(x_22, x_16);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
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
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Syntax_getArg(x_22, x_14);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__3(x_1, x_17, x_15, x_28, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_1);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__3(x_1, x_17, x_15, x_31, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
lean_dec(x_1);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrindTrace___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalGrindTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalGrindTrace", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrindTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalGrindTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Config(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__3 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__3);
l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4 = _init_l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__3);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__1);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__2);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__1);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__2);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__3);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__4);
l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__5);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__3);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__4 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__4();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___closed__4);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4);
l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2___closed__1 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__2___closed__1);
l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1 = _init_l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__1 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__1();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__1);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__2 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__2();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__2);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__3 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__3();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__3);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__4 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__4();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__4);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__5 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__5();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__5);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__6 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__6();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___closed__6);
l_Lean_Elab_Tactic_elabGrindPattern___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindPattern___closed__1);
l_Lean_Elab_Tactic_elabGrindPattern___closed__2 = _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindPattern___closed__2);
l_Lean_Elab_Tactic_elabGrindPattern___closed__3 = _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindPattern___closed__3);
l_Lean_Elab_Tactic_elabGrindPattern___closed__4 = _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindPattern___closed__4);
l_Lean_Elab_Tactic_elabGrindPattern___closed__5 = _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindPattern___closed__5);
l_Lean_Elab_Tactic_elabGrindPattern___closed__6 = _init_l_Lean_Elab_Tactic_elabGrindPattern___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindPattern___closed__6);
l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___closed__1 = _init_l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabResetGrindAttrs___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_elabResetGrindAttrs__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_elabInitGrindNorm___closed__1 = _init_l_Lean_Elab_Tactic_elabInitGrindNorm___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabInitGrindNorm___closed__1);
l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2 = _init_l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2);
l_Lean_Elab_Tactic_elabInitGrindNorm___boxed__const__1 = _init_l_Lean_Elab_Tactic_elabInitGrindNorm___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabInitGrindNorm___boxed__const__1);
l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__1);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__2);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__3);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__1);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__3);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__4);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__1 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__1);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__3 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__3);
l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4 = _init_l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__2___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__3___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___lambda__4___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__5___closed__9);
l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__1);
l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2);
l_Lean_Elab_Tactic_mkGrindParams___closed__1 = _init_l_Lean_Elab_Tactic_mkGrindParams___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkGrindParams___closed__1);
l_Lean_Elab_Tactic_grind___closed__1 = _init_l_Lean_Elab_Tactic_grind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_grind___closed__1);
l_Lean_Elab_Tactic_grind___closed__2 = _init_l_Lean_Elab_Tactic_grind___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_grind___closed__2);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__1 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__1);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__2 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__2);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__3 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__3);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__4 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__4);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__5 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__5);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__6 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__6);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__7 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__7);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__8 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__8);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__11 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__11);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__12 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__12);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__17 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__17();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__17);
l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18 = _init_l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18);
l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindCore___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalGrindCore___closed__1 = _init_l_Lean_Elab_Tactic_evalGrindCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindCore___closed__1);
l_Lean_Elab_Tactic_evalGrindCore___closed__2 = _init_l_Lean_Elab_Tactic_evalGrindCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindCore___closed__2);
l_Lean_Elab_Tactic_evalGrindCore___closed__3 = _init_l_Lean_Elab_Tactic_evalGrindCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindCore___closed__3);
l_Lean_Elab_Tactic_evalGrindCore___closed__4 = _init_l_Lean_Elab_Tactic_evalGrindCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindCore___closed__4);
l_Lean_Elab_Tactic_grindParamsPos = _init_l_Lean_Elab_Tactic_grindParamsPos();
lean_mark_persistent(l_Lean_Elab_Tactic_grindParamsPos);
l_Lean_Elab_Tactic_grindOnlyPos = _init_l_Lean_Elab_Tactic_grindOnlyPos();
lean_mark_persistent(l_Lean_Elab_Tactic_grindOnlyPos);
l_Lean_Elab_Tactic_isGrindOnly___closed__1 = _init_l_Lean_Elab_Tactic_isGrindOnly___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_isGrindOnly___closed__1);
l_Lean_Elab_Tactic_isGrindOnly___closed__2 = _init_l_Lean_Elab_Tactic_isGrindOnly___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_isGrindOnly___closed__2);
l_Lean_Elab_Tactic_setGrindParams___closed__1 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__1);
l_Lean_Elab_Tactic_setGrindParams___closed__2 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__2);
l_Lean_Elab_Tactic_setGrindParams___closed__3 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__3);
l_Lean_Elab_Tactic_setGrindParams___closed__4 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__4);
l_Lean_Elab_Tactic_setGrindParams___closed__5 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__5);
l_Lean_Elab_Tactic_setGrindParams___closed__6 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__6);
l_Lean_Elab_Tactic_setGrindParams___closed__7 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__7);
l_Lean_Elab_Tactic_setGrindParams___closed__8 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__8);
l_Lean_Elab_Tactic_setGrindParams___closed__9 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__9);
l_Lean_Elab_Tactic_setGrindParams___closed__10 = _init_l_Lean_Elab_Tactic_setGrindParams___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_setGrindParams___closed__10);
l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_toList___at_Lean_Elab_Tactic_mkGrindOnly___spec__2___closed__1);
l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___closed__1 = _init_l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobal_unresolveNameCore___at_Lean_Elab_Tactic_mkGrindOnly___spec__7___lambda__2___closed__1);
l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___closed__1 = _init_l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobal___at_Lean_Elab_Tactic_mkGrindOnly___spec__6___lambda__1___closed__1);
l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__1 = _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__1);
l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__2 = _init_l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Lean_unresolveNameGlobalAvoidingLocals___at_Lean_Elab_Tactic_mkGrindOnly___spec__5___lambda__1___closed__2);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__1);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__2);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__3);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__4);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__5);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__6);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__7 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__7();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__7);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__8);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__9 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__9();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__9);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__10);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__11 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__11();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__11);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__12);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__13);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__14 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__14();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__14);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__15);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__16);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__17 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__17();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__17);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__18);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__19);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__20 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__20();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__20);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__21);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__22 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__22();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__22);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__23);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__24 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__24();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__24);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__25);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__26 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__26();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__26);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__27);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__28);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__29 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__29();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__29);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__30);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__31 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__31();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__31);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__32);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__33);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__34 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__34();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__34);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__35);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__11___closed__36);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__1);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__2);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__3);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__16___closed__4);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__1);
l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Elab_Tactic_mkGrindOnly___spec__17___closed__2);
l_Lean_Elab_Tactic_mkGrindOnly___closed__1 = _init_l_Lean_Elab_Tactic_mkGrindOnly___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkGrindOnly___closed__1);
l_Lean_Elab_Tactic_mkGrindOnly___closed__2 = _init_l_Lean_Elab_Tactic_mkGrindOnly___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_mkGrindOnly___closed__2);
l_Lean_Elab_Tactic_mkGrindOnly___closed__3 = _init_l_Lean_Elab_Tactic_mkGrindOnly___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_mkGrindOnly___closed__3);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg___closed__2);
l_Lean_Elab_Tactic_evalGrind___closed__1 = _init_l_Lean_Elab_Tactic_evalGrind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___closed__1);
l_Lean_Elab_Tactic_evalGrind___closed__2 = _init_l_Lean_Elab_Tactic_evalGrind___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindTrace___lambda__1___closed__3);
l_Lean_Elab_Tactic_evalGrindTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalGrindTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindTrace___closed__1);
l_Lean_Elab_Tactic_evalGrindTrace___closed__2 = _init_l_Lean_Elab_Tactic_evalGrindTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrindTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalGrindTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
