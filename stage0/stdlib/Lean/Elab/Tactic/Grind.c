// Lean compiler output
// Module: Lean.Elab.Tactic.Grind
// Imports: Init.Grind.Tactics Lean.Meta.Tactic.Grind Lean.Elab.Command Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Config
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1(lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__4;
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_grind___closed__2;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalGrind___closed__2;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addEMatchTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__1;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__2;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerNormTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_7799_(uint8_t, uint8_t);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__7;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_grind___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__2;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2;
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__17;
static lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__1;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__1;
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_List_filterMapTR_go___at_Lean_preprocessSyntaxAndResolve___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrind___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindConfig___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_filterFieldList___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessPattern(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__11;
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabInitGrindNorm___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getDeclName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toPArray_x27___rarg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Result_hasFailures(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Tactic_Config_0__Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__3;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalGrind___closed__3;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Tactic_mkGrindParams___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalGrind___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__6;
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsUsingDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__15;
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveLocalName_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__7;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__1;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__14;
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__3;
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4;
lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__3;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___rarg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___closed__4;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__16;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1(lean_object*);
static lean_object* l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabInitGrindNorm__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__4;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_grind(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__4;
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Result_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAndSynthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getCasesTypes___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2(lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__3;
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___closed__2;
static lean_object* l_Lean_Elab_Tactic_elabGrindPattern___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_elabGrindPattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4;
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Grind_instInhabitedEMatchTheorems___spec__1;
lean_object* l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__1;
extern lean_object* l_Lean_instInhabitedName;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__6;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_addTermInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___elambda__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__10;
lean_object* l_Lean_Elab_Tactic_liftMetaFinishingTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindPattern(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback_unsafe__1___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabInitGrindNorm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__6;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Elab_Term_expandDeclId___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__4;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__9;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__3;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__3;
lean_object* l_List_filterTR_loop___at_Lean_filterFieldList___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback___closed__18;
static lean_object* l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getEMatchTheorems___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(5u);
x_3 = lean_unsigned_to_nat(1000u);
x_4 = 1;
x_5 = 0;
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_6);
lean_ctor_set(x_7, 5, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 1, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 2, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*6 + 4, x_4);
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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = 0;
x_10 = l_Lean_MessageData_ofConstName(x_1, x_9);
x_11 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___lambda__1(x_11, x_10, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
x_15 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected identifier", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4;
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
x_37 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__3;
x_38 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__8(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___closed__1;
x_10 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_Lean_instInhabitedName;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1;
x_2 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__2;
x_3 = lean_unsigned_to_nat(364u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous identifier '", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', possible interpretations: ", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__4;
x_11 = l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_23 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__5;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__6;
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
x_35 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(x_1, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_elabGrindPattern___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___boxed), 8, 0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg___lambda__1), 10, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg___boxed), 10, 0);
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
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__12(x_2, x_4, x_14, x_15, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_4);
x_20 = lean_array_to_list(x_17);
x_21 = l_Lean_Meta_Grind_addEMatchTheorem(x_3, x_19, x_20, x_8, x_9, x_10, x_11, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
x_10 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Tactic_elabGrindPattern___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_26 = l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg(x_24, x_25, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
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
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg(x_4);
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
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg(x_4);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_filterFieldList___at_Lean_Elab_Tactic_elabGrindPattern___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___at_Lean_Elab_Tactic_elabGrindPattern___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at_Lean_Elab_Tactic_elabGrindPattern___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Tactic_elabGrindPattern___spec__12(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_forallTelescope___at_Lean_Elab_Tactic_elabGrindPattern___spec__13___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg(x_4);
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
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_7799_(x_3, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = 6;
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_7799_(x_3, x_12);
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
x_1 = lean_mk_string_unchecked("` is not a theorem, definition, or inductive type", 49, 49);
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
x_1 = lean_mk_string_unchecked("` is a reducible definition, `grind` automatically unfolds them", 63, 63);
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
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l_Lean_isReducible___at___private_Lean_Meta_Basic_0__Lean_Meta_getDefInfoTemp___spec__1(x_2, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2(x_2, x_1, x_3, x_16, x_4, x_5, x_6, x_7, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = l_Lean_MessageData_ofName(x_2);
x_22 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4;
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_22);
x_23 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_24, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_dec(x_12);
x_31 = l_Lean_MessageData_ofName(x_2);
x_32 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__1___closed__4;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_35, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
case 2:
{
lean_object* x_41; uint8_t x_42; uint8_t x_43; 
lean_dec(x_10);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_dec(x_9);
x_42 = 2;
x_43 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_7799_(x_3, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_1);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_1, 3);
x_49 = l_Lean_PersistentArray_push___rarg(x_48, x_47);
lean_ctor_set(x_1, 3, x_49);
lean_ctor_set(x_44, 0, x_1);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
x_53 = lean_ctor_get(x_1, 2);
x_54 = lean_ctor_get(x_1, 3);
x_55 = lean_ctor_get(x_1, 4);
x_56 = lean_ctor_get(x_1, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_57 = l_Lean_PersistentArray_push___rarg(x_54, x_50);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_52);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 4, x_55);
lean_ctor_set(x_58, 5, x_56);
lean_ctor_set(x_44, 0, x_58);
return x_44;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_44, 0);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_44);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 4);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 5);
lean_inc(x_66);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 x_67 = x_1;
} else {
 lean_dec_ref(x_1);
 x_67 = lean_box(0);
}
x_68 = l_Lean_PersistentArray_push___rarg(x_64, x_59);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 6, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_63);
lean_ctor_set(x_69, 3, x_68);
lean_ctor_set(x_69, 4, x_65);
lean_ctor_set(x_69, 5, x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_60);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_44);
if (x_71 == 0)
{
return x_44;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_44, 0);
x_73 = lean_ctor_get(x_44, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_44);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; lean_object* x_76; 
x_75 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_76 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_75, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = !lean_is_exclusive(x_1);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_ctor_get(x_1, 1);
x_82 = lean_ctor_get(x_1, 2);
x_83 = lean_ctor_get(x_1, 3);
x_84 = lean_ctor_get(x_1, 4);
x_85 = lean_ctor_get(x_1, 5);
x_86 = l_Lean_PersistentArray_push___rarg(x_83, x_77);
x_87 = 1;
x_88 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_87, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = l_Lean_PersistentArray_push___rarg(x_86, x_90);
lean_ctor_set(x_1, 3, x_91);
lean_ctor_set(x_88, 0, x_1);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
x_94 = l_Lean_PersistentArray_push___rarg(x_86, x_92);
lean_ctor_set(x_1, 3, x_94);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_86);
lean_free_object(x_1);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
return x_88;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_1, 0);
x_101 = lean_ctor_get(x_1, 1);
x_102 = lean_ctor_get(x_1, 2);
x_103 = lean_ctor_get(x_1, 3);
x_104 = lean_ctor_get(x_1, 4);
x_105 = lean_ctor_get(x_1, 5);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_1);
x_106 = l_Lean_PersistentArray_push___rarg(x_103, x_77);
x_107 = 1;
x_108 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_2, x_107, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = l_Lean_PersistentArray_push___rarg(x_106, x_109);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_100);
lean_ctor_set(x_113, 1, x_101);
lean_ctor_set(x_113, 2, x_102);
lean_ctor_set(x_113, 3, x_112);
lean_ctor_set(x_113, 4, x_104);
lean_ctor_set(x_113, 5, x_105);
if (lean_is_scalar(x_111)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_111;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_117 = x_108;
} else {
 lean_dec_ref(x_108);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_76);
if (x_119 == 0)
{
return x_76;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_76, 0);
x_121 = lean_ctor_get(x_76, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_76);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
default: 
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_10);
lean_dec(x_1);
x_123 = lean_ctor_get(x_9, 1);
lean_inc(x_123);
lean_dec(x_9);
x_124 = l_Lean_MessageData_ofName(x_2);
x_125 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___lambda__2___closed__2;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___closed__2;
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_throwError___at_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem___spec__1(x_128, x_4, x_5, x_6, x_7, x_123);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_9);
if (x_130 == 0)
{
return x_9;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_9, 0);
x_132 = lean_ctor_get(x_9, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_9);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get_uint8(x_4, 0);
x_12 = lean_ctor_get(x_7, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_7, 5, x_13);
x_14 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_3, x_2, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_26 = lean_ctor_get_uint8(x_4, 0);
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 4);
x_32 = lean_ctor_get(x_7, 5);
x_33 = lean_ctor_get(x_7, 6);
x_34 = lean_ctor_get(x_7, 7);
x_35 = lean_ctor_get(x_7, 8);
x_36 = lean_ctor_get(x_7, 9);
x_37 = lean_ctor_get(x_7, 10);
x_38 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_39 = lean_ctor_get(x_7, 11);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_39);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_41 = l_Lean_replaceRef(x_1, x_32);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_28);
lean_ctor_set(x_42, 2, x_29);
lean_ctor_set(x_42, 3, x_30);
lean_ctor_set(x_42, 4, x_31);
lean_ctor_set(x_42, 5, x_41);
lean_ctor_set(x_42, 6, x_33);
lean_ctor_set(x_42, 7, x_34);
lean_ctor_set(x_42, 8, x_35);
lean_ctor_set(x_42, 9, x_36);
lean_ctor_set(x_42, 10, x_37);
lean_ctor_set(x_42, 11, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*12, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*12 + 1, x_40);
x_43 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_3, x_2, x_26, x_5, x_6, x_42, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_51 = x_43;
} else {
 lean_dec_ref(x_43);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
case 1:
{
uint8_t x_53; 
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get_uint8(x_4, 0);
x_55 = lean_ctor_get(x_7, 5);
x_56 = l_Lean_replaceRef(x_1, x_55);
lean_dec(x_55);
lean_ctor_set(x_7, 5, x_56);
lean_inc(x_2);
x_57 = l_Lean_Meta_Grind_validateCasesAttr(x_2, x_54, x_7, x_8, x_9);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_3, 2);
x_62 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_61, x_2, x_54);
lean_ctor_set(x_3, 2, x_62);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_57, 0, x_63);
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_3, 0);
x_65 = lean_ctor_get(x_3, 1);
x_66 = lean_ctor_get(x_3, 2);
x_67 = lean_ctor_get(x_3, 3);
x_68 = lean_ctor_get(x_3, 4);
x_69 = lean_ctor_get(x_3, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_3);
x_70 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_66, x_2, x_54);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_57, 0, x_72);
return x_57;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_57, 1);
lean_inc(x_73);
lean_dec(x_57);
x_74 = lean_ctor_get(x_3, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 5);
lean_inc(x_79);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_80 = x_3;
} else {
 lean_dec_ref(x_3);
 x_80 = lean_box(0);
}
x_81 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_76, x_2, x_54);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_75);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_77);
lean_ctor_set(x_82, 4, x_78);
lean_ctor_set(x_82, 5, x_79);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_73);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_57);
if (x_85 == 0)
{
return x_57;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_57, 0);
x_87 = lean_ctor_get(x_57, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_57);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_89 = lean_ctor_get_uint8(x_4, 0);
x_90 = lean_ctor_get(x_7, 0);
x_91 = lean_ctor_get(x_7, 1);
x_92 = lean_ctor_get(x_7, 2);
x_93 = lean_ctor_get(x_7, 3);
x_94 = lean_ctor_get(x_7, 4);
x_95 = lean_ctor_get(x_7, 5);
x_96 = lean_ctor_get(x_7, 6);
x_97 = lean_ctor_get(x_7, 7);
x_98 = lean_ctor_get(x_7, 8);
x_99 = lean_ctor_get(x_7, 9);
x_100 = lean_ctor_get(x_7, 10);
x_101 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_102 = lean_ctor_get(x_7, 11);
x_103 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_102);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_7);
x_104 = l_Lean_replaceRef(x_1, x_95);
lean_dec(x_95);
x_105 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_105, 0, x_90);
lean_ctor_set(x_105, 1, x_91);
lean_ctor_set(x_105, 2, x_92);
lean_ctor_set(x_105, 3, x_93);
lean_ctor_set(x_105, 4, x_94);
lean_ctor_set(x_105, 5, x_104);
lean_ctor_set(x_105, 6, x_96);
lean_ctor_set(x_105, 7, x_97);
lean_ctor_set(x_105, 8, x_98);
lean_ctor_set(x_105, 9, x_99);
lean_ctor_set(x_105, 10, x_100);
lean_ctor_set(x_105, 11, x_102);
lean_ctor_set_uint8(x_105, sizeof(void*)*12, x_101);
lean_ctor_set_uint8(x_105, sizeof(void*)*12 + 1, x_103);
lean_inc(x_2);
x_106 = l_Lean_Meta_Grind_validateCasesAttr(x_2, x_89, x_105, x_8, x_9);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_3, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_3, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_3, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_3, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_3, 4);
lean_inc(x_113);
x_114 = lean_ctor_get(x_3, 5);
lean_inc(x_114);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_115 = x_3;
} else {
 lean_dec_ref(x_3);
 x_115 = lean_box(0);
}
x_116 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_111, x_2, x_89);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 6, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_109);
lean_ctor_set(x_117, 1, x_110);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_117, 3, x_112);
lean_ctor_set(x_117, 4, x_113);
lean_ctor_set(x_117, 5, x_114);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
if (lean_is_scalar(x_108)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_108;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_107);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_106, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_106, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_122 = x_106;
} else {
 lean_dec_ref(x_106);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
default: 
{
uint8_t x_124; lean_object* x_125; 
x_124 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_125 = l_Lean_Meta_Grind_isCasesAttrCandidate(x_2, x_124, x_7, x_8, x_9);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = !lean_is_exclusive(x_7);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_7, 5);
x_131 = l_Lean_replaceRef(x_1, x_130);
lean_dec(x_130);
lean_ctor_set(x_7, 5, x_131);
x_132 = 6;
x_133 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_3, x_2, x_132, x_5, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_133, 0, x_136);
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_133, 0);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_133);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_133);
if (x_141 == 0)
{
return x_133;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_133, 0);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_133);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_145 = lean_ctor_get(x_7, 0);
x_146 = lean_ctor_get(x_7, 1);
x_147 = lean_ctor_get(x_7, 2);
x_148 = lean_ctor_get(x_7, 3);
x_149 = lean_ctor_get(x_7, 4);
x_150 = lean_ctor_get(x_7, 5);
x_151 = lean_ctor_get(x_7, 6);
x_152 = lean_ctor_get(x_7, 7);
x_153 = lean_ctor_get(x_7, 8);
x_154 = lean_ctor_get(x_7, 9);
x_155 = lean_ctor_get(x_7, 10);
x_156 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_157 = lean_ctor_get(x_7, 11);
x_158 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_157);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_7);
x_159 = l_Lean_replaceRef(x_1, x_150);
lean_dec(x_150);
x_160 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_160, 0, x_145);
lean_ctor_set(x_160, 1, x_146);
lean_ctor_set(x_160, 2, x_147);
lean_ctor_set(x_160, 3, x_148);
lean_ctor_set(x_160, 4, x_149);
lean_ctor_set(x_160, 5, x_159);
lean_ctor_set(x_160, 6, x_151);
lean_ctor_set(x_160, 7, x_152);
lean_ctor_set(x_160, 8, x_153);
lean_ctor_set(x_160, 9, x_154);
lean_ctor_set(x_160, 10, x_155);
lean_ctor_set(x_160, 11, x_157);
lean_ctor_set_uint8(x_160, sizeof(void*)*12, x_156);
lean_ctor_set_uint8(x_160, sizeof(void*)*12 + 1, x_158);
x_161 = 6;
x_162 = l_Lean_Elab_Tactic_elabGrindParams_addEMatchTheorem(x_3, x_2, x_161, x_5, x_6, x_160, x_8, x_128);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_163);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_162, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_162, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_170 = x_162;
} else {
 lean_dec_ref(x_162);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_172 = !lean_is_exclusive(x_125);
if (x_172 == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_125, 0);
lean_dec(x_173);
x_174 = !lean_is_exclusive(x_3);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_3, 2);
x_176 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_175, x_2, x_124);
lean_ctor_set(x_3, 2, x_176);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_125, 0, x_177);
return x_125;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_3, 0);
x_179 = lean_ctor_get(x_3, 1);
x_180 = lean_ctor_get(x_3, 2);
x_181 = lean_ctor_get(x_3, 3);
x_182 = lean_ctor_get(x_3, 4);
x_183 = lean_ctor_get(x_3, 5);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_3);
x_184 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_180, x_2, x_124);
x_185 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_185, 0, x_178);
lean_ctor_set(x_185, 1, x_179);
lean_ctor_set(x_185, 2, x_184);
lean_ctor_set(x_185, 3, x_181);
lean_ctor_set(x_185, 4, x_182);
lean_ctor_set(x_185, 5, x_183);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_125, 0, x_186);
return x_125;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_187 = lean_ctor_get(x_125, 1);
lean_inc(x_187);
lean_dec(x_125);
x_188 = lean_ctor_get(x_3, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_3, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_3, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_3, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_3, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_3, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 x_194 = x_3;
} else {
 lean_dec_ref(x_3);
 x_194 = lean_box(0);
}
x_195 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Grind_CasesTypes_insert___spec__1(x_190, x_2, x_124);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 6, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_188);
lean_ctor_set(x_196, 1, x_189);
lean_ctor_set(x_196, 2, x_195);
lean_ctor_set(x_196, 3, x_191);
lean_ctor_set(x_196, 4, x_192);
lean_ctor_set(x_196, 5, x_193);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_187);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_199 = !lean_is_exclusive(x_125);
if (x_199 == 0)
{
return x_125;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_125, 0);
x_201 = lean_ctor_get(x_125, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_125);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected `grind` parameter", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Elab_Tactic_elabGrindPattern___closed__6;
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_15 = l_Lean_MessageData_ofSyntax(x_2);
x_16 = l_Lean_indentD(x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_20, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_12, x_26, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(2);
x_31 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__1(x_2, x_28, x_3, x_30, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_Meta_Grind_getAttrKindCore(x_34, x_8, x_9, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__1(x_2, x_32, x_3, x_36, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_36);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindParam", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindErase", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindLemma", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Attr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grindMod", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__7;
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; uint8_t x_25; 
x_14 = lean_array_uget(x_3, x_5);
x_24 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__2;
lean_inc(x_14);
x_25 = l_Lean_Syntax_isOfKind(x_14, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_6);
x_26 = l_Lean_MessageData_ofSyntax(x_14);
x_27 = l_Lean_indentD(x_26);
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_31, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_14, x_37);
x_39 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__4;
lean_inc(x_38);
x_40 = l_Lean_Syntax_isOfKind(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__6;
lean_inc(x_38);
x_42 = l_Lean_Syntax_isOfKind(x_38, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_38);
lean_dec(x_6);
x_43 = l_Lean_MessageData_ofSyntax(x_14);
x_44 = l_Lean_indentD(x_43);
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_48, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Syntax_getArg(x_38, x_37);
x_55 = l_Lean_Syntax_isNone(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_unsigned_to_nat(1u);
lean_inc(x_54);
x_57 = l_Lean_Syntax_matchesNull(x_54, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_54);
lean_dec(x_38);
lean_dec(x_6);
x_58 = l_Lean_MessageData_ofSyntax(x_14);
x_59 = l_Lean_indentD(x_58);
x_60 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_63, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = l_Lean_Syntax_getArg(x_54, x_37);
lean_dec(x_54);
x_70 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__9;
lean_inc(x_69);
x_71 = l_Lean_Syntax_isOfKind(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_69);
lean_dec(x_38);
lean_dec(x_6);
x_72 = l_Lean_MessageData_ofSyntax(x_14);
x_73 = l_Lean_indentD(x_72);
x_74 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_77, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_69);
x_84 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_85 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2(x_38, x_14, x_6, x_84, x_83, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_38);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_15 = x_86;
x_16 = x_87;
goto block_23;
}
else
{
uint8_t x_88; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_85);
if (x_88 == 0)
{
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_85);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_54);
x_92 = lean_box(0);
x_93 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_94 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2(x_38, x_14, x_6, x_93, x_92, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_38);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_15 = x_95;
x_16 = x_96;
goto block_23;
}
else
{
uint8_t x_97; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_94);
if (x_97 == 0)
{
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_unsigned_to_nat(1u);
x_102 = l_Lean_Syntax_getArg(x_38, x_101);
lean_dec(x_38);
x_103 = l_Lean_Elab_Tactic_elabGrindPattern___closed__6;
lean_inc(x_102);
x_104 = l_Lean_Syntax_isOfKind(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_102);
lean_dec(x_6);
x_105 = l_Lean_MessageData_ofSyntax(x_14);
x_106 = l_Lean_indentD(x_105);
x_107 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_110, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_14);
x_116 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_117 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_102, x_116, x_9, x_10, x_11);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_118);
x_121 = l_Lean_Meta_Grind_isCasesAttrCandidate(x_118, x_120, x_9, x_10, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = !lean_is_exclusive(x_6);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_6, 0);
x_127 = lean_ctor_get(x_6, 1);
x_128 = lean_ctor_get(x_6, 2);
x_129 = lean_ctor_get(x_6, 3);
x_130 = lean_ctor_get(x_6, 4);
x_131 = lean_ctor_get(x_6, 5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_132 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_127, x_118, x_7, x_8, x_9, x_10, x_124);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_ctor_set(x_6, 1, x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_6);
x_15 = x_135;
x_16 = x_134;
goto block_23;
}
else
{
uint8_t x_136; 
lean_free_object(x_6);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_140 = lean_ctor_get(x_6, 0);
x_141 = lean_ctor_get(x_6, 1);
x_142 = lean_ctor_get(x_6, 2);
x_143 = lean_ctor_get(x_6, 3);
x_144 = lean_ctor_get(x_6, 4);
x_145 = lean_ctor_get(x_6, 5);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_146 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_141, x_118, x_7, x_8, x_9, x_10, x_124);
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
x_15 = x_150;
x_16 = x_148;
goto block_23;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
lean_dec(x_121);
x_156 = !lean_is_exclusive(x_6);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_6, 0);
x_158 = lean_ctor_get(x_6, 1);
x_159 = lean_ctor_get(x_6, 2);
x_160 = lean_ctor_get(x_6, 3);
x_161 = lean_ctor_get(x_6, 4);
x_162 = lean_ctor_get(x_6, 5);
x_163 = l_Lean_Meta_Grind_CasesTypes_eraseDecl(x_159, x_118, x_9, x_10, x_155);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_ctor_set(x_6, 2, x_164);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_6);
x_15 = x_166;
x_16 = x_165;
goto block_23;
}
else
{
uint8_t x_167; 
lean_free_object(x_6);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_167 = !lean_is_exclusive(x_163);
if (x_167 == 0)
{
return x_163;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_163, 0);
x_169 = lean_ctor_get(x_163, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_163);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_6, 0);
x_172 = lean_ctor_get(x_6, 1);
x_173 = lean_ctor_get(x_6, 2);
x_174 = lean_ctor_get(x_6, 3);
x_175 = lean_ctor_get(x_6, 4);
x_176 = lean_ctor_get(x_6, 5);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_6);
x_177 = l_Lean_Meta_Grind_CasesTypes_eraseDecl(x_173, x_118, x_9, x_10, x_155);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_180, 0, x_171);
lean_ctor_set(x_180, 1, x_172);
lean_ctor_set(x_180, 2, x_178);
lean_ctor_set(x_180, 3, x_174);
lean_ctor_set(x_180, 4, x_175);
lean_ctor_set(x_180, 5, x_176);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_15 = x_181;
x_16 = x_179;
goto block_23;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_182 = lean_ctor_get(x_177, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_177, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_184 = x_177;
} else {
 lean_dec_ref(x_177);
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
}
}
else
{
uint8_t x_186; 
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_186 = !lean_is_exclusive(x_121);
if (x_186 == 0)
{
return x_121;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_121, 0);
x_188 = lean_ctor_get(x_121, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_121);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_190 = !lean_is_exclusive(x_117);
if (x_190 == 0)
{
return x_117;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_117, 0);
x_192 = lean_ctor_get(x_117, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_117);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
x_11 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(x_2, x_8, x_2, x_9, x_10, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabGrindParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_elabGrindParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
lean_ctor_set(x_1, 2, x_4);
lean_ctor_set(x_1, 1, x_2);
x_13 = l_Lean_Elab_Tactic_elabGrindParams(x_1, x_3, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_4);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_17);
x_19 = l_Lean_Elab_Tactic_elabGrindParams(x_18, x_3, x_5, x_6, x_7, x_8, x_9);
return x_19;
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
x_13 = l_Lean_Elab_Tactic_mkGrindParams___lambda__1(x_1, x_4, x_2, x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Tactic_mkGrindParams___lambda__2___closed__2;
x_15 = l_Lean_Elab_Tactic_mkGrindParams___lambda__1(x_1, x_4, x_2, x_14, x_5, x_6, x_7, x_8, x_9);
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
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkGrindParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_mkGrindParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
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
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Meta_Grind_Result_hasFailures(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; 
lean_free_object(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_Grind_Result_toMessageData(x_17, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_28 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_27, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = l_Lean_Meta_Grind_Result_hasFailures(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Meta_Grind_Result_toMessageData(x_33, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Tactic_grind___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_43 = l_Lean_Elab_Tactic_elabGrindConfig___lambda__1___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_44, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_48 = x_38;
} else {
 lean_dec_ref(x_38);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_12);
if (x_54 == 0)
{
return x_12;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_12);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalGrind___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_grind(x_6, x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Elab_Tactic_grind(x_5, x_1, x_11, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Elab_Tactic_grind(x_5, x_1, x_11, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The `grind` tactic is experimental and still under development. Avoid using it in production projects", 101, 101);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_grind", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Elab_Tactic_Grind_0__Lean_Elab_Tactic_elabFallback(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__3;
x_20 = 1;
lean_inc(x_13);
x_21 = l_Lean_logAt___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__2(x_1, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_dec(x_21);
x_54 = l_Lean_Elab_Term_getDeclName_x3f(x_9, x_10, x_11, x_12, x_13, x_14, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_57 = l_Lean_Elab_Tactic_elabGrindConfig(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_55) == 0)
{
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4;
x_61 = l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5;
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind___lambda__2___boxed), 10, 4);
lean_closure_set(x_62, 0, x_58);
lean_closure_set(x_62, 1, x_60);
lean_closure_set(x_62, 2, x_61);
lean_closure_set(x_62, 3, x_17);
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_63, 0, x_62);
x_64 = l_Lean_Elab_Tactic_withMainContext___rarg(x_63, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_59);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_57);
if (x_65 == 0)
{
return x_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_57);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_55, 0);
lean_inc(x_69);
lean_dec(x_55);
x_70 = lean_ctor_get(x_57, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_dec(x_57);
x_72 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4;
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind___lambda__2___boxed), 10, 4);
lean_closure_set(x_73, 0, x_70);
lean_closure_set(x_73, 1, x_72);
lean_closure_set(x_73, 2, x_69);
lean_closure_set(x_73, 3, x_17);
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_74, 0, x_73);
x_75 = l_Lean_Elab_Tactic_withMainContext___rarg(x_74, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_71);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_55);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_76 = !lean_is_exclusive(x_57);
if (x_76 == 0)
{
return x_57;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_57, 0);
x_78 = lean_ctor_get(x_57, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_57);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_4, 0);
x_81 = 0;
x_22 = x_81;
x_23 = x_80;
goto block_52;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_21, 1);
lean_inc(x_82);
lean_dec(x_21);
x_83 = l_Lean_Elab_Term_getDeclName_x3f(x_9, x_10, x_11, x_12, x_13, x_14, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_86 = l_Lean_Elab_Tactic_elabGrindConfig(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_85);
if (lean_obj_tag(x_84) == 0)
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4;
x_90 = l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5;
x_91 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind___lambda__3___boxed), 10, 4);
lean_closure_set(x_91, 0, x_87);
lean_closure_set(x_91, 1, x_89);
lean_closure_set(x_91, 2, x_90);
lean_closure_set(x_91, 3, x_17);
x_92 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_92, 0, x_91);
x_93 = l_Lean_Elab_Tactic_withMainContext___rarg(x_92, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_88);
return x_93;
}
else
{
uint8_t x_94; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
return x_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_84, 0);
lean_inc(x_98);
lean_dec(x_84);
x_99 = lean_ctor_get(x_86, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_86, 1);
lean_inc(x_100);
lean_dec(x_86);
x_101 = l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4;
x_102 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind___lambda__3___boxed), 10, 4);
lean_closure_set(x_102, 0, x_99);
lean_closure_set(x_102, 1, x_101);
lean_closure_set(x_102, 2, x_98);
lean_closure_set(x_102, 3, x_17);
x_103 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_103, 0, x_102);
x_104 = l_Lean_Elab_Tactic_withMainContext___rarg(x_103, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_100);
return x_104;
}
else
{
uint8_t x_105; 
lean_dec(x_84);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_105 = !lean_is_exclusive(x_86);
if (x_105 == 0)
{
return x_86;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_86, 0);
x_107 = lean_ctor_get(x_86, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_86);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_4, 0);
x_110 = 1;
x_22 = x_110;
x_23 = x_109;
goto block_52;
}
}
block_52:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Syntax_TSepArray_getElems___rarg(x_23);
x_26 = l_Lean_Elab_Term_getDeclName_x3f(x_9, x_10, x_11, x_12, x_13, x_14, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Elab_Tactic_elabGrindConfig(x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
if (lean_obj_tag(x_27) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5;
x_33 = lean_box(x_22);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind___lambda__1___boxed), 11, 5);
lean_closure_set(x_34, 0, x_30);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_25);
lean_closure_set(x_34, 3, x_32);
lean_closure_set(x_34, 4, x_17);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = l_Lean_Elab_Tactic_withMainContext___rarg(x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_27, 0);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_box(x_22);
x_45 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalGrind___lambda__1___boxed), 11, 5);
lean_closure_set(x_45, 0, x_42);
lean_closure_set(x_45, 1, x_44);
lean_closure_set(x_45, 2, x_25);
lean_closure_set(x_45, 3, x_41);
lean_closure_set(x_45, 4, x_17);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaFinishingTactic), 10, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = l_Lean_Elab_Tactic_withMainContext___rarg(x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_43);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_29, 0);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_29);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_16);
if (x_111 == 0)
{
return x_16;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_16, 0);
x_113 = lean_ctor_get(x_16, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_16);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_25 = l_Lean_Elab_Tactic_evalGrind___lambda__4(x_1, x_2, x_3, x_5, x_24, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_26 = lean_box(0);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Tactic_evalGrind___lambda__4(x_1, x_2, x_3, x_5, x_27, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_24 = l_Lean_Elab_Tactic_evalGrind___lambda__5(x_1, x_2, x_4, x_23, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_27 = l_Lean_Elab_Tactic_evalGrind___lambda__5(x_1, x_2, x_4, x_26, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
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
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalGrind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalUnsafe____x40_Lean_Elab_Tactic_Grind___hyg_5____closed__1;
x_2 = l_Lean_Elab_Tactic_elabGrindPattern___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Tactic_elabGrindPattern__1___closed__2;
x_4 = l_Lean_Elab_Tactic_evalGrind___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalGrind___closed__2;
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
x_16 = l_Lean_Elab_Tactic_evalGrind___closed__4;
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
x_28 = l_Lean_Elab_Tactic_evalGrind___lambda__6(x_1, x_15, x_27, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_31 = l_Lean_Elab_Tactic_evalGrind___lambda__6(x_1, x_15, x_30, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Tactic_evalGrind___lambda__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalGrind___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalGrind___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_evalGrind___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_evalGrind___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalGrind___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalGrind___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_3 = l_Lean_Elab_Tactic_evalGrind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalGrind__1___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin, lean_object*);
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
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_elabGrindPattern___spec__1___rarg___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__3);
l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Tactic_elabGrindPattern___spec__6___closed__4);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__1 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__1();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__1);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__2 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__2();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__2);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__3 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__3();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__3);
l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4 = _init_l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4();
lean_mark_persistent(l_Lean_preprocessSyntaxAndResolve___at_Lean_Elab_Tactic_elabGrindPattern___spec__7___closed__4);
l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___closed__1 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Tactic_elabGrindPattern___spec__3___closed__1);
l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___closed__1 = _init_l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Tactic_elabGrindPattern___spec__10___closed__1);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__1);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__2 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__2();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__2);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__3 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__3();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__3);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__4 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__4();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__4);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__5 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__5();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__5);
l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__6 = _init_l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__6();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___at_Lean_Elab_Tactic_elabGrindPattern___spec__9___closed__6);
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
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___lambda__2___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__3);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__4);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__5);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__6);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__7);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__8);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Tactic_elabGrindParams___spec__1___closed__9);
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
l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__1);
l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__2);
l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__3);
l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__4 = _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__4);
l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5 = _init_l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___lambda__4___closed__5);
l_Lean_Elab_Tactic_evalGrind___closed__1 = _init_l_Lean_Elab_Tactic_evalGrind___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___closed__1);
l_Lean_Elab_Tactic_evalGrind___closed__2 = _init_l_Lean_Elab_Tactic_evalGrind___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___closed__2);
l_Lean_Elab_Tactic_evalGrind___closed__3 = _init_l_Lean_Elab_Tactic_evalGrind___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___closed__3);
l_Lean_Elab_Tactic_evalGrind___closed__4 = _init_l_Lean_Elab_Tactic_evalGrind___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalGrind___closed__4);
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
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
