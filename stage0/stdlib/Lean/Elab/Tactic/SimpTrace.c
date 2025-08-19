// Lean compiler output
// Module: Lean.Elab.Tactic.SimpTrace
// Imports: Lean.Elab.ElabRules Lean.Elab.Tactic.Simp Lean.Meta.Tactic.TryThis
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0;
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__13;
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3;
lean_object* l_Array_mkArray0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__0;
lean_object* l_Array_mkArray1___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12;
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4;
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__6;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setAutoUnfold(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__1;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6;
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0;
static lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Syntax_unsetTrailing(x_1);
x_9 = l_Lean_Elab_Tactic_mkSimpOnly(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_mkSimpCallStx(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_mk_empty_array_with_capacity(x_2);
x_17 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_3);
x_18 = l_Lean_Elab_Tactic_simpLocation(x_4, x_5, x_6, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l_Lean_Elab_Tactic_expandLocation(x_19);
x_21 = l_Lean_Elab_Tactic_simpLocation(x_4, x_5, x_6, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAutoUnfold", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp!", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (x_1 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_483; uint8_t x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_568; uint8_t x_569; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_2, x_18);
x_507 = lean_unsigned_to_nat(1u);
x_568 = l_Lean_Syntax_getArg(x_2, x_507);
x_569 = l_Lean_Syntax_isNone(x_568);
if (x_569 == 0)
{
uint8_t x_570; 
lean_inc(x_568);
x_570 = l_Lean_Syntax_matchesNull(x_568, x_507);
if (x_570 == 0)
{
lean_object* x_571; 
lean_dec(x_568);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_571 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_16);
return x_571;
}
else
{
lean_object* x_572; lean_object* x_573; 
x_572 = l_Lean_Syntax_getArg(x_568, x_18);
lean_dec(x_568);
x_573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_573, 0, x_572);
x_538 = x_573;
x_539 = x_8;
x_540 = x_9;
x_541 = x_10;
x_542 = x_11;
x_543 = x_12;
x_544 = x_13;
x_545 = x_14;
x_546 = x_15;
x_547 = x_16;
goto block_567;
}
}
else
{
lean_object* x_574; 
lean_dec(x_568);
x_574 = lean_box(0);
x_538 = x_574;
x_539 = x_8;
x_540 = x_9;
x_541 = x_10;
x_542 = x_11;
x_543 = x_12;
x_544 = x_13;
x_545 = x_14;
x_546 = x_15;
x_547 = x_16;
goto block_567;
}
block_92:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_box(x_3);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(x_35, 0, x_22);
lean_closure_set(x_35, 1, x_18);
lean_closure_set(x_35, 2, x_34);
lean_closure_set(x_35, 3, x_33);
lean_closure_set(x_35, 4, x_20);
lean_inc(x_29);
lean_inc_ref(x_32);
lean_inc(x_28);
lean_inc_ref(x_23);
x_36 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_21, x_35, x_24, x_27, x_26, x_31, x_23, x_28, x_32, x_29, x_25);
lean_dec(x_21);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 0);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_29);
lean_inc_ref(x_32);
lean_inc(x_28);
lean_inc_ref(x_23);
x_42 = l_Lean_Elab_Tactic_mkSimpCallStx(x_30, x_40, x_23, x_28, x_32, x_29, x_38);
lean_dec_ref(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_32, 5);
x_46 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
lean_ctor_set(x_37, 1, x_43);
lean_ctor_set(x_37, 0, x_46);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_48, 0, x_37);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set(x_48, 5, x_47);
lean_inc(x_45);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_45);
x_50 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_51 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_19, x_48, x_49, x_50, x_47, x_23, x_28, x_32, x_29, x_44);
lean_dec(x_28);
lean_dec_ref(x_23);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_41);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_41);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_41);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_37);
lean_dec_ref(x_41);
lean_dec_ref(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_23);
lean_dec(x_19);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_37, 0);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_37);
lean_inc(x_29);
lean_inc_ref(x_32);
lean_inc(x_28);
lean_inc_ref(x_23);
x_66 = l_Lean_Elab_Tactic_mkSimpCallStx(x_30, x_64, x_23, x_28, x_32, x_29, x_38);
lean_dec_ref(x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec_ref(x_66);
x_69 = lean_ctor_get(x_32, 5);
x_70 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_73, 4, x_72);
lean_ctor_set(x_73, 5, x_72);
lean_inc(x_69);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_69);
x_75 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_76 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_19, x_73, x_74, x_75, x_72, x_23, x_28, x_32, x_29, x_68);
lean_dec(x_28);
lean_dec_ref(x_23);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_65);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_65);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_82 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_65);
lean_dec_ref(x_32);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_23);
lean_dec(x_19);
x_84 = lean_ctor_get(x_66, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_66, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_86 = x_66;
} else {
 lean_dec_ref(x_66);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_23);
lean_dec(x_19);
x_88 = !lean_is_exclusive(x_36);
if (x_88 == 0)
{
return x_36;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_36, 0);
x_90 = lean_ctor_get(x_36, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_36);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
block_128:
{
uint8_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
x_106 = 0;
x_107 = 0;
x_108 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
lean_inc(x_104);
lean_inc_ref(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_100);
lean_inc_ref(x_99);
lean_inc(x_98);
lean_inc_ref(x_97);
x_109 = l_Lean_Elab_Tactic_mkSimpContext(x_96, x_106, x_107, x_106, x_108, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec_ref(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_110, 2);
lean_inc(x_114);
lean_dec(x_110);
x_20 = x_113;
x_21 = x_114;
x_22 = x_93;
x_23 = x_101;
x_24 = x_97;
x_25 = x_111;
x_26 = x_99;
x_27 = x_98;
x_28 = x_102;
x_29 = x_104;
x_30 = x_96;
x_31 = x_100;
x_32 = x_103;
x_33 = x_112;
goto block_92;
}
else
{
lean_dec_ref(x_95);
if (x_94 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_dec_ref(x_109);
x_116 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_110, 2);
lean_inc(x_118);
lean_dec(x_110);
x_20 = x_117;
x_21 = x_118;
x_22 = x_93;
x_23 = x_101;
x_24 = x_97;
x_25 = x_115;
x_26 = x_99;
x_27 = x_98;
x_28 = x_102;
x_29 = x_104;
x_30 = x_96;
x_31 = x_100;
x_32 = x_103;
x_33 = x_116;
goto block_92;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_109, 1);
lean_inc(x_119);
lean_dec_ref(x_109);
x_120 = lean_ctor_get(x_110, 0);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_110, 1);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_110, 2);
lean_inc(x_122);
lean_dec(x_110);
x_123 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_120);
x_20 = x_121;
x_21 = x_122;
x_22 = x_93;
x_23 = x_101;
x_24 = x_97;
x_25 = x_119;
x_26 = x_99;
x_27 = x_98;
x_28 = x_102;
x_29 = x_104;
x_30 = x_96;
x_31 = x_100;
x_32 = x_103;
x_33 = x_123;
goto block_92;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_19);
x_124 = !lean_is_exclusive(x_109);
if (x_124 == 0)
{
return x_109;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_109, 0);
x_126 = lean_ctor_get(x_109, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_109);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
block_154:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = l_Array_append___redArg(x_149, x_150);
lean_dec_ref(x_150);
lean_inc(x_134);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_134);
lean_ctor_set(x_152, 1, x_147);
lean_ctor_set(x_152, 2, x_151);
x_153 = l_Lean_Syntax_node6(x_134, x_138, x_132, x_145, x_135, x_148, x_130, x_152);
x_93 = x_129;
x_94 = x_131;
x_95 = x_143;
x_96 = x_153;
x_97 = x_144;
x_98 = x_146;
x_99 = x_140;
x_100 = x_136;
x_101 = x_142;
x_102 = x_139;
x_103 = x_141;
x_104 = x_137;
x_105 = x_133;
goto block_128;
}
block_183:
{
lean_object* x_177; lean_object* x_178; 
lean_inc_ref(x_175);
x_177 = l_Array_append___redArg(x_175, x_176);
lean_dec_ref(x_176);
lean_inc(x_173);
lean_inc(x_160);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_160);
lean_ctor_set(x_178, 1, x_173);
lean_ctor_set(x_178, 2, x_177);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_179; 
x_179 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_129 = x_155;
x_130 = x_178;
x_131 = x_157;
x_132 = x_158;
x_133 = x_159;
x_134 = x_160;
x_135 = x_161;
x_136 = x_162;
x_137 = x_163;
x_138 = x_164;
x_139 = x_165;
x_140 = x_166;
x_141 = x_167;
x_142 = x_168;
x_143 = x_169;
x_144 = x_170;
x_145 = x_172;
x_146 = x_171;
x_147 = x_173;
x_148 = x_174;
x_149 = x_175;
x_150 = x_179;
goto block_154;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_156, 0);
lean_inc(x_180);
lean_dec_ref(x_156);
x_181 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_182 = lean_array_push(x_181, x_180);
x_129 = x_155;
x_130 = x_178;
x_131 = x_157;
x_132 = x_158;
x_133 = x_159;
x_134 = x_160;
x_135 = x_161;
x_136 = x_162;
x_137 = x_163;
x_138 = x_164;
x_139 = x_165;
x_140 = x_166;
x_141 = x_167;
x_142 = x_168;
x_143 = x_169;
x_144 = x_170;
x_145 = x_172;
x_146 = x_171;
x_147 = x_173;
x_148 = x_174;
x_149 = x_175;
x_150 = x_182;
goto block_154;
}
}
block_217:
{
lean_object* x_206; lean_object* x_207; 
lean_inc_ref(x_204);
x_206 = l_Array_append___redArg(x_204, x_205);
lean_dec_ref(x_205);
lean_inc(x_203);
lean_inc(x_189);
x_207 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_207, 0, x_189);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_206);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_208; 
x_208 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_190;
x_162 = x_191;
x_163 = x_192;
x_164 = x_193;
x_165 = x_194;
x_166 = x_195;
x_167 = x_196;
x_168 = x_198;
x_169 = x_199;
x_170 = x_200;
x_171 = x_202;
x_172 = x_201;
x_173 = x_203;
x_174 = x_207;
x_175 = x_204;
x_176 = x_208;
goto block_183;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_209 = lean_ctor_get(x_197, 0);
lean_inc(x_209);
lean_dec_ref(x_197);
x_210 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_189);
x_211 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_211, 0, x_189);
lean_ctor_set(x_211, 1, x_210);
lean_inc_ref(x_204);
x_212 = l_Array_append___redArg(x_204, x_209);
lean_dec(x_209);
lean_inc(x_203);
lean_inc(x_189);
x_213 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_213, 0, x_189);
lean_ctor_set(x_213, 1, x_203);
lean_ctor_set(x_213, 2, x_212);
x_214 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_189);
x_215 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_215, 0, x_189);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_Array_mkArray3___redArg(x_211, x_213, x_215);
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_190;
x_162 = x_191;
x_163 = x_192;
x_164 = x_193;
x_165 = x_194;
x_166 = x_195;
x_167 = x_196;
x_168 = x_198;
x_169 = x_199;
x_170 = x_200;
x_171 = x_202;
x_172 = x_201;
x_173 = x_203;
x_174 = x_207;
x_175 = x_204;
x_176 = x_216;
goto block_183;
}
}
block_248:
{
lean_object* x_240; lean_object* x_241; 
lean_inc_ref(x_238);
x_240 = l_Array_append___redArg(x_238, x_239);
lean_dec_ref(x_239);
lean_inc(x_237);
lean_inc(x_223);
x_241 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_241, 0, x_223);
lean_ctor_set(x_241, 1, x_237);
lean_ctor_set(x_241, 2, x_240);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_242; 
x_242 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_184 = x_218;
x_185 = x_219;
x_186 = x_220;
x_187 = x_221;
x_188 = x_222;
x_189 = x_223;
x_190 = x_241;
x_191 = x_224;
x_192 = x_225;
x_193 = x_226;
x_194 = x_227;
x_195 = x_228;
x_196 = x_229;
x_197 = x_232;
x_198 = x_231;
x_199 = x_233;
x_200 = x_234;
x_201 = x_236;
x_202 = x_235;
x_203 = x_237;
x_204 = x_238;
x_205 = x_242;
goto block_217;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_230, 0);
lean_inc(x_243);
lean_dec_ref(x_230);
x_244 = l_Lean_SourceInfo_fromRef(x_243, x_3);
lean_dec(x_243);
x_245 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_246 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Array_mkArray1___redArg(x_246);
x_184 = x_218;
x_185 = x_219;
x_186 = x_220;
x_187 = x_221;
x_188 = x_222;
x_189 = x_223;
x_190 = x_241;
x_191 = x_224;
x_192 = x_225;
x_193 = x_226;
x_194 = x_227;
x_195 = x_228;
x_196 = x_229;
x_197 = x_232;
x_198 = x_231;
x_199 = x_233;
x_200 = x_234;
x_201 = x_236;
x_202 = x_235;
x_203 = x_237;
x_204 = x_238;
x_205 = x_247;
goto block_217;
}
}
block_274:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = l_Array_append___redArg(x_252, x_270);
lean_dec_ref(x_270);
lean_inc(x_269);
x_272 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_253);
lean_ctor_set(x_272, 2, x_271);
x_273 = l_Lean_Syntax_node6(x_269, x_257, x_255, x_266, x_267, x_250, x_264, x_272);
x_93 = x_249;
x_94 = x_251;
x_95 = x_263;
x_96 = x_273;
x_97 = x_265;
x_98 = x_268;
x_99 = x_259;
x_100 = x_254;
x_101 = x_262;
x_102 = x_258;
x_103 = x_261;
x_104 = x_256;
x_105 = x_260;
goto block_128;
}
block_302:
{
lean_object* x_297; lean_object* x_298; 
lean_inc_ref(x_279);
x_297 = l_Array_append___redArg(x_279, x_296);
lean_dec_ref(x_296);
lean_inc(x_280);
lean_inc(x_295);
x_298 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_280);
lean_ctor_set(x_298, 2, x_297);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_299; 
lean_dec_ref(x_7);
x_299 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_249 = x_275;
x_250 = x_277;
x_251 = x_278;
x_252 = x_279;
x_253 = x_280;
x_254 = x_281;
x_255 = x_282;
x_256 = x_283;
x_257 = x_284;
x_258 = x_285;
x_259 = x_286;
x_260 = x_287;
x_261 = x_288;
x_262 = x_289;
x_263 = x_290;
x_264 = x_298;
x_265 = x_291;
x_266 = x_294;
x_267 = x_293;
x_268 = x_292;
x_269 = x_295;
x_270 = x_299;
goto block_274;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_276, 0);
lean_inc(x_300);
lean_dec_ref(x_276);
x_301 = lean_apply_1(x_7, x_300);
x_249 = x_275;
x_250 = x_277;
x_251 = x_278;
x_252 = x_279;
x_253 = x_280;
x_254 = x_281;
x_255 = x_282;
x_256 = x_283;
x_257 = x_284;
x_258 = x_285;
x_259 = x_286;
x_260 = x_287;
x_261 = x_288;
x_262 = x_289;
x_263 = x_290;
x_264 = x_298;
x_265 = x_291;
x_266 = x_294;
x_267 = x_293;
x_268 = x_292;
x_269 = x_295;
x_270 = x_301;
goto block_274;
}
}
block_336:
{
lean_object* x_325; lean_object* x_326; 
lean_inc_ref(x_306);
x_325 = l_Array_append___redArg(x_306, x_324);
lean_dec_ref(x_324);
lean_inc(x_307);
lean_inc(x_323);
x_326 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_307);
lean_ctor_set(x_326, 2, x_325);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_327; 
x_327 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_275 = x_303;
x_276 = x_304;
x_277 = x_326;
x_278 = x_305;
x_279 = x_306;
x_280 = x_307;
x_281 = x_308;
x_282 = x_309;
x_283 = x_310;
x_284 = x_311;
x_285 = x_312;
x_286 = x_313;
x_287 = x_314;
x_288 = x_315;
x_289 = x_317;
x_290 = x_318;
x_291 = x_319;
x_292 = x_322;
x_293 = x_321;
x_294 = x_320;
x_295 = x_323;
x_296 = x_327;
goto block_302;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_328 = lean_ctor_get(x_316, 0);
lean_inc(x_328);
lean_dec_ref(x_316);
x_329 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_323);
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_323);
lean_ctor_set(x_330, 1, x_329);
lean_inc_ref(x_306);
x_331 = l_Array_append___redArg(x_306, x_328);
lean_dec(x_328);
lean_inc(x_307);
lean_inc(x_323);
x_332 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_332, 0, x_323);
lean_ctor_set(x_332, 1, x_307);
lean_ctor_set(x_332, 2, x_331);
x_333 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_323);
x_334 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_334, 0, x_323);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Array_mkArray3___redArg(x_330, x_332, x_334);
x_275 = x_303;
x_276 = x_304;
x_277 = x_326;
x_278 = x_305;
x_279 = x_306;
x_280 = x_307;
x_281 = x_308;
x_282 = x_309;
x_283 = x_310;
x_284 = x_311;
x_285 = x_312;
x_286 = x_313;
x_287 = x_314;
x_288 = x_315;
x_289 = x_317;
x_290 = x_318;
x_291 = x_319;
x_292 = x_322;
x_293 = x_321;
x_294 = x_320;
x_295 = x_323;
x_296 = x_335;
goto block_302;
}
}
block_367:
{
lean_object* x_359; lean_object* x_360; 
lean_inc_ref(x_340);
x_359 = l_Array_append___redArg(x_340, x_358);
lean_dec_ref(x_358);
lean_inc(x_341);
lean_inc(x_357);
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_341);
lean_ctor_set(x_360, 2, x_359);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_361; 
x_361 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_303 = x_337;
x_304 = x_338;
x_305 = x_339;
x_306 = x_340;
x_307 = x_341;
x_308 = x_342;
x_309 = x_343;
x_310 = x_344;
x_311 = x_345;
x_312 = x_346;
x_313 = x_347;
x_314 = x_348;
x_315 = x_349;
x_316 = x_352;
x_317 = x_351;
x_318 = x_353;
x_319 = x_354;
x_320 = x_356;
x_321 = x_360;
x_322 = x_355;
x_323 = x_357;
x_324 = x_361;
goto block_336;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_362 = lean_ctor_get(x_350, 0);
lean_inc(x_362);
lean_dec_ref(x_350);
x_363 = l_Lean_SourceInfo_fromRef(x_362, x_3);
lean_dec(x_362);
x_364 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_365 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = l_Array_mkArray1___redArg(x_365);
x_303 = x_337;
x_304 = x_338;
x_305 = x_339;
x_306 = x_340;
x_307 = x_341;
x_308 = x_342;
x_309 = x_343;
x_310 = x_344;
x_311 = x_345;
x_312 = x_346;
x_313 = x_347;
x_314 = x_348;
x_315 = x_349;
x_316 = x_352;
x_317 = x_351;
x_318 = x_353;
x_319 = x_354;
x_320 = x_356;
x_321 = x_360;
x_322 = x_355;
x_323 = x_357;
x_324 = x_366;
goto block_336;
}
}
block_412:
{
lean_object* x_386; uint8_t x_387; 
x_386 = lean_st_ref_get(x_372, x_383);
x_387 = !lean_is_exclusive(x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_388 = lean_ctor_get(x_386, 1);
x_389 = lean_ctor_get(x_386, 0);
lean_dec(x_389);
x_390 = lean_ctor_get(x_375, 5);
x_391 = l_Lean_SourceInfo_fromRef(x_390, x_385);
x_392 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
x_393 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_392);
x_394 = l_Lean_SourceInfo_fromRef(x_19, x_3);
lean_ctor_set_tag(x_386, 2);
lean_ctor_set(x_386, 1, x_392);
lean_ctor_set(x_386, 0, x_394);
x_395 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_396 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_397; 
x_397 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_218 = x_368;
x_219 = x_369;
x_220 = x_370;
x_221 = x_386;
x_222 = x_388;
x_223 = x_391;
x_224 = x_371;
x_225 = x_372;
x_226 = x_393;
x_227 = x_373;
x_228 = x_374;
x_229 = x_375;
x_230 = x_376;
x_231 = x_377;
x_232 = x_378;
x_233 = x_379;
x_234 = x_380;
x_235 = x_382;
x_236 = x_381;
x_237 = x_395;
x_238 = x_396;
x_239 = x_397;
goto block_248;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_384, 0);
lean_inc(x_398);
lean_dec_ref(x_384);
x_399 = l_Array_mkArray1___redArg(x_398);
x_218 = x_368;
x_219 = x_369;
x_220 = x_370;
x_221 = x_386;
x_222 = x_388;
x_223 = x_391;
x_224 = x_371;
x_225 = x_372;
x_226 = x_393;
x_227 = x_373;
x_228 = x_374;
x_229 = x_375;
x_230 = x_376;
x_231 = x_377;
x_232 = x_378;
x_233 = x_379;
x_234 = x_380;
x_235 = x_382;
x_236 = x_381;
x_237 = x_395;
x_238 = x_396;
x_239 = x_399;
goto block_248;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_400 = lean_ctor_get(x_386, 1);
lean_inc(x_400);
lean_dec(x_386);
x_401 = lean_ctor_get(x_375, 5);
x_402 = l_Lean_SourceInfo_fromRef(x_401, x_385);
x_403 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
x_404 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_403);
x_405 = l_Lean_SourceInfo_fromRef(x_19, x_3);
x_406 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_403);
x_407 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_408 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_409; 
x_409 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_218 = x_368;
x_219 = x_369;
x_220 = x_370;
x_221 = x_406;
x_222 = x_400;
x_223 = x_402;
x_224 = x_371;
x_225 = x_372;
x_226 = x_404;
x_227 = x_373;
x_228 = x_374;
x_229 = x_375;
x_230 = x_376;
x_231 = x_377;
x_232 = x_378;
x_233 = x_379;
x_234 = x_380;
x_235 = x_382;
x_236 = x_381;
x_237 = x_407;
x_238 = x_408;
x_239 = x_409;
goto block_248;
}
else
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_384, 0);
lean_inc(x_410);
lean_dec_ref(x_384);
x_411 = l_Array_mkArray1___redArg(x_410);
x_218 = x_368;
x_219 = x_369;
x_220 = x_370;
x_221 = x_406;
x_222 = x_400;
x_223 = x_402;
x_224 = x_371;
x_225 = x_372;
x_226 = x_404;
x_227 = x_373;
x_228 = x_374;
x_229 = x_375;
x_230 = x_376;
x_231 = x_377;
x_232 = x_378;
x_233 = x_379;
x_234 = x_380;
x_235 = x_382;
x_236 = x_381;
x_237 = x_407;
x_238 = x_408;
x_239 = x_411;
goto block_248;
}
}
}
block_460:
{
if (lean_obj_tag(x_421) == 0)
{
uint8_t x_429; 
lean_dec_ref(x_7);
x_429 = 0;
lean_inc(x_422);
x_368 = x_422;
x_369 = x_422;
x_370 = x_420;
x_371 = x_415;
x_372 = x_426;
x_373 = x_423;
x_374 = x_418;
x_375 = x_427;
x_376 = x_416;
x_377 = x_417;
x_378 = x_425;
x_379 = x_421;
x_380 = x_424;
x_381 = x_414;
x_382 = x_419;
x_383 = x_413;
x_384 = x_428;
x_385 = x_429;
goto block_412;
}
else
{
if (x_420 == 0)
{
lean_dec_ref(x_7);
lean_inc(x_422);
x_368 = x_422;
x_369 = x_422;
x_370 = x_420;
x_371 = x_415;
x_372 = x_426;
x_373 = x_423;
x_374 = x_418;
x_375 = x_427;
x_376 = x_416;
x_377 = x_417;
x_378 = x_425;
x_379 = x_421;
x_380 = x_424;
x_381 = x_414;
x_382 = x_419;
x_383 = x_413;
x_384 = x_428;
x_385 = x_420;
goto block_412;
}
else
{
lean_object* x_430; uint8_t x_431; 
x_430 = lean_st_ref_get(x_426, x_413);
x_431 = !lean_is_exclusive(x_430);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_432 = lean_ctor_get(x_430, 1);
x_433 = lean_ctor_get(x_430, 0);
lean_dec(x_433);
x_434 = lean_ctor_get(x_427, 5);
x_435 = 0;
x_436 = l_Lean_SourceInfo_fromRef(x_434, x_435);
x_437 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11;
x_438 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_437);
x_439 = l_Lean_SourceInfo_fromRef(x_19, x_3);
x_440 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12;
lean_ctor_set_tag(x_430, 2);
lean_ctor_set(x_430, 1, x_440);
lean_ctor_set(x_430, 0, x_439);
x_441 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_442 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_443; 
x_443 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
lean_inc(x_422);
x_337 = x_422;
x_338 = x_422;
x_339 = x_420;
x_340 = x_442;
x_341 = x_441;
x_342 = x_415;
x_343 = x_430;
x_344 = x_426;
x_345 = x_438;
x_346 = x_423;
x_347 = x_418;
x_348 = x_432;
x_349 = x_427;
x_350 = x_416;
x_351 = x_417;
x_352 = x_425;
x_353 = x_421;
x_354 = x_424;
x_355 = x_419;
x_356 = x_414;
x_357 = x_436;
x_358 = x_443;
goto block_367;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_428, 0);
lean_inc(x_444);
lean_dec_ref(x_428);
lean_inc_ref(x_7);
x_445 = lean_apply_1(x_7, x_444);
lean_inc(x_422);
x_337 = x_422;
x_338 = x_422;
x_339 = x_420;
x_340 = x_442;
x_341 = x_441;
x_342 = x_415;
x_343 = x_430;
x_344 = x_426;
x_345 = x_438;
x_346 = x_423;
x_347 = x_418;
x_348 = x_432;
x_349 = x_427;
x_350 = x_416;
x_351 = x_417;
x_352 = x_425;
x_353 = x_421;
x_354 = x_424;
x_355 = x_419;
x_356 = x_414;
x_357 = x_436;
x_358 = x_445;
goto block_367;
}
}
else
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_446 = lean_ctor_get(x_430, 1);
lean_inc(x_446);
lean_dec(x_430);
x_447 = lean_ctor_get(x_427, 5);
x_448 = 0;
x_449 = l_Lean_SourceInfo_fromRef(x_447, x_448);
x_450 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11;
x_451 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_450);
x_452 = l_Lean_SourceInfo_fromRef(x_19, x_3);
x_453 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12;
x_454 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_456 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_457; 
x_457 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
lean_inc(x_422);
x_337 = x_422;
x_338 = x_422;
x_339 = x_420;
x_340 = x_456;
x_341 = x_455;
x_342 = x_415;
x_343 = x_454;
x_344 = x_426;
x_345 = x_451;
x_346 = x_423;
x_347 = x_418;
x_348 = x_446;
x_349 = x_427;
x_350 = x_416;
x_351 = x_417;
x_352 = x_425;
x_353 = x_421;
x_354 = x_424;
x_355 = x_419;
x_356 = x_414;
x_357 = x_449;
x_358 = x_457;
goto block_367;
}
else
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_428, 0);
lean_inc(x_458);
lean_dec_ref(x_428);
lean_inc_ref(x_7);
x_459 = lean_apply_1(x_7, x_458);
lean_inc(x_422);
x_337 = x_422;
x_338 = x_422;
x_339 = x_420;
x_340 = x_456;
x_341 = x_455;
x_342 = x_415;
x_343 = x_454;
x_344 = x_426;
x_345 = x_451;
x_346 = x_423;
x_347 = x_418;
x_348 = x_446;
x_349 = x_427;
x_350 = x_416;
x_351 = x_417;
x_352 = x_425;
x_353 = x_421;
x_354 = x_424;
x_355 = x_419;
x_356 = x_414;
x_357 = x_449;
x_358 = x_459;
goto block_367;
}
}
}
}
}
block_482:
{
lean_object* x_477; 
x_477 = l_Lean_Syntax_getOptional_x3f(x_463);
lean_dec(x_463);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; 
x_478 = lean_box(0);
x_413 = x_474;
x_414 = x_473;
x_415 = x_462;
x_416 = x_468;
x_417 = x_469;
x_418 = x_466;
x_419 = x_475;
x_420 = x_461;
x_421 = x_471;
x_422 = x_476;
x_423 = x_465;
x_424 = x_472;
x_425 = x_470;
x_426 = x_464;
x_427 = x_467;
x_428 = x_478;
goto block_460;
}
else
{
uint8_t x_479; 
x_479 = !lean_is_exclusive(x_477);
if (x_479 == 0)
{
x_413 = x_474;
x_414 = x_473;
x_415 = x_462;
x_416 = x_468;
x_417 = x_469;
x_418 = x_466;
x_419 = x_475;
x_420 = x_461;
x_421 = x_471;
x_422 = x_476;
x_423 = x_465;
x_424 = x_472;
x_425 = x_470;
x_426 = x_464;
x_427 = x_467;
x_428 = x_477;
goto block_460;
}
else
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_ctor_get(x_477, 0);
lean_inc(x_480);
lean_dec(x_477);
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_480);
x_413 = x_474;
x_414 = x_473;
x_415 = x_462;
x_416 = x_468;
x_417 = x_469;
x_418 = x_466;
x_419 = x_475;
x_420 = x_461;
x_421 = x_471;
x_422 = x_476;
x_423 = x_465;
x_424 = x_472;
x_425 = x_470;
x_426 = x_464;
x_427 = x_467;
x_428 = x_481;
goto block_460;
}
}
}
block_506:
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_unsigned_to_nat(4u);
x_500 = l_Lean_Syntax_getArg(x_485, x_499);
lean_dec(x_485);
x_501 = l_Lean_Syntax_getOptional_x3f(x_500);
lean_dec(x_500);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; 
x_502 = lean_box(0);
x_461 = x_484;
x_462 = x_493;
x_463 = x_483;
x_464 = x_497;
x_465 = x_495;
x_466 = x_492;
x_467 = x_496;
x_468 = x_486;
x_469 = x_494;
x_470 = x_489;
x_471 = x_487;
x_472 = x_490;
x_473 = x_488;
x_474 = x_498;
x_475 = x_491;
x_476 = x_502;
goto block_482;
}
else
{
uint8_t x_503; 
x_503 = !lean_is_exclusive(x_501);
if (x_503 == 0)
{
x_461 = x_484;
x_462 = x_493;
x_463 = x_483;
x_464 = x_497;
x_465 = x_495;
x_466 = x_492;
x_467 = x_496;
x_468 = x_486;
x_469 = x_494;
x_470 = x_489;
x_471 = x_487;
x_472 = x_490;
x_473 = x_488;
x_474 = x_498;
x_475 = x_491;
x_476 = x_501;
goto block_482;
}
else
{
lean_object* x_504; lean_object* x_505; 
x_504 = lean_ctor_get(x_501, 0);
lean_inc(x_504);
lean_dec(x_501);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_504);
x_461 = x_484;
x_462 = x_493;
x_463 = x_483;
x_464 = x_497;
x_465 = x_495;
x_466 = x_492;
x_467 = x_496;
x_468 = x_486;
x_469 = x_494;
x_470 = x_489;
x_471 = x_487;
x_472 = x_490;
x_473 = x_488;
x_474 = x_498;
x_475 = x_491;
x_476 = x_505;
goto block_482;
}
}
}
block_537:
{
lean_object* x_523; lean_object* x_524; uint8_t x_525; 
x_523 = lean_unsigned_to_nat(3u);
x_524 = l_Lean_Syntax_getArg(x_510, x_523);
x_525 = l_Lean_Syntax_isNone(x_524);
if (x_525 == 0)
{
uint8_t x_526; 
lean_inc(x_524);
x_526 = l_Lean_Syntax_matchesNull(x_524, x_507);
if (x_526 == 0)
{
lean_object* x_527; 
lean_dec(x_524);
lean_dec(x_521);
lean_dec_ref(x_520);
lean_dec(x_519);
lean_dec_ref(x_518);
lean_dec(x_517);
lean_dec_ref(x_516);
lean_dec(x_515);
lean_dec_ref(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_508);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_527 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_522);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; 
x_528 = l_Lean_Syntax_getArg(x_524, x_18);
lean_dec(x_524);
x_529 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_530 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_529);
lean_inc(x_528);
x_531 = l_Lean_Syntax_isOfKind(x_528, x_530);
lean_dec(x_530);
if (x_531 == 0)
{
lean_object* x_532; 
lean_dec(x_528);
lean_dec(x_521);
lean_dec_ref(x_520);
lean_dec(x_519);
lean_dec_ref(x_518);
lean_dec(x_517);
lean_dec_ref(x_516);
lean_dec(x_515);
lean_dec_ref(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_508);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_532 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_522);
return x_532;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = l_Lean_Syntax_getArg(x_528, x_507);
lean_dec(x_528);
x_534 = l_Lean_Syntax_getArgs(x_533);
lean_dec(x_533);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_534);
x_483 = x_508;
x_484 = x_509;
x_485 = x_510;
x_486 = x_513;
x_487 = x_511;
x_488 = x_512;
x_489 = x_535;
x_490 = x_514;
x_491 = x_515;
x_492 = x_516;
x_493 = x_517;
x_494 = x_518;
x_495 = x_519;
x_496 = x_520;
x_497 = x_521;
x_498 = x_522;
goto block_506;
}
}
}
else
{
lean_object* x_536; 
lean_dec(x_524);
x_536 = lean_box(0);
x_483 = x_508;
x_484 = x_509;
x_485 = x_510;
x_486 = x_513;
x_487 = x_511;
x_488 = x_512;
x_489 = x_536;
x_490 = x_514;
x_491 = x_515;
x_492 = x_516;
x_493 = x_517;
x_494 = x_518;
x_495 = x_519;
x_496 = x_520;
x_497 = x_521;
x_498 = x_522;
goto block_506;
}
}
block_567:
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; 
x_548 = lean_unsigned_to_nat(2u);
x_549 = l_Lean_Syntax_getArg(x_2, x_548);
x_550 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_551 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_550);
lean_inc(x_549);
x_552 = l_Lean_Syntax_isOfKind(x_549, x_551);
lean_dec(x_551);
if (x_552 == 0)
{
lean_object* x_553; 
lean_dec(x_549);
lean_dec(x_546);
lean_dec_ref(x_545);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec(x_538);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_553 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_547);
return x_553;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; uint8_t x_557; 
x_554 = l_Lean_Syntax_getArg(x_549, x_18);
x_555 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_556 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_555);
lean_inc(x_554);
x_557 = l_Lean_Syntax_isOfKind(x_554, x_556);
lean_dec(x_556);
if (x_557 == 0)
{
lean_object* x_558; 
lean_dec(x_554);
lean_dec(x_549);
lean_dec(x_546);
lean_dec_ref(x_545);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec(x_538);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_558 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_547);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; uint8_t x_561; 
x_559 = l_Lean_Syntax_getArg(x_549, x_507);
x_560 = l_Lean_Syntax_getArg(x_549, x_548);
x_561 = l_Lean_Syntax_isNone(x_560);
if (x_561 == 0)
{
uint8_t x_562; 
lean_inc(x_560);
x_562 = l_Lean_Syntax_matchesNull(x_560, x_507);
if (x_562 == 0)
{
lean_object* x_563; 
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_554);
lean_dec(x_549);
lean_dec(x_546);
lean_dec_ref(x_545);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec_ref(x_541);
lean_dec(x_540);
lean_dec_ref(x_539);
lean_dec(x_538);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_563 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_547);
return x_563;
}
else
{
lean_object* x_564; lean_object* x_565; 
x_564 = l_Lean_Syntax_getArg(x_560, x_18);
lean_dec(x_560);
x_565 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_565, 0, x_564);
x_508 = x_559;
x_509 = x_557;
x_510 = x_549;
x_511 = x_538;
x_512 = x_554;
x_513 = x_565;
x_514 = x_539;
x_515 = x_540;
x_516 = x_541;
x_517 = x_542;
x_518 = x_543;
x_519 = x_544;
x_520 = x_545;
x_521 = x_546;
x_522 = x_547;
goto block_537;
}
}
else
{
lean_object* x_566; 
lean_dec(x_560);
x_566 = lean_box(0);
x_508 = x_559;
x_509 = x_557;
x_510 = x_549;
x_511 = x_538;
x_512 = x_554;
x_513 = x_566;
x_514 = x_539;
x_515 = x_540;
x_516 = x_541;
x_517 = x_542;
x_518 = x_543;
x_519 = x_544;
x_520 = x_545;
x_521 = x_546;
x_522 = x_547;
goto block_537;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpTrace", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___closed__3;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__0), 1, 0);
x_12 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_13 = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_14 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_15 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
lean_inc(x_1);
x_16 = l_Lean_Syntax_isOfKind(x_1, x_15);
x_17 = 1;
x_18 = lean_box(x_16);
x_19 = lean_box(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed), 16, 7);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_12);
lean_closure_set(x_20, 4, x_13);
lean_closure_set(x_20, 5, x_14);
lean_closure_set(x_20, 6, x_11);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Lean_Elab_Tactic_withMainContext___redArg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
x_17 = l_Lean_Elab_Tactic_evalSimpTrace___lam__1(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_1);
x_18 = lean_unbox(x_3);
x_19 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2(x_17, x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_2);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpTrace", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_3 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(28u);
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = lean_unsigned_to_nat(25u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(45u);
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(32u);
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5;
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3;
x_3 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__5;
x_2 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__6;
x_2 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAll", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_all", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAllAutoUnfold", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_all!", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAllTraceArgsRest", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_511; uint8_t x_512; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_450 = lean_unsigned_to_nat(1u);
x_511 = l_Lean_Syntax_getArg(x_2, x_450);
x_512 = l_Lean_Syntax_isNone(x_511);
if (x_512 == 0)
{
uint8_t x_513; 
lean_inc(x_511);
x_513 = l_Lean_Syntax_matchesNull(x_511, x_450);
if (x_513 == 0)
{
lean_object* x_514; 
lean_dec(x_511);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_514 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_15);
return x_514;
}
else
{
lean_object* x_515; lean_object* x_516; 
x_515 = l_Lean_Syntax_getArg(x_511, x_17);
lean_dec(x_511);
x_516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_516, 0, x_515);
x_481 = x_516;
x_482 = x_7;
x_483 = x_8;
x_484 = x_9;
x_485 = x_10;
x_486 = x_11;
x_487 = x_12;
x_488 = x_13;
x_489 = x_14;
x_490 = x_15;
goto block_510;
}
}
else
{
lean_object* x_517; 
lean_dec(x_511);
x_517 = lean_box(0);
x_481 = x_517;
x_482 = x_7;
x_483 = x_8;
x_484 = x_9;
x_485 = x_10;
x_486 = x_11;
x_487 = x_12;
x_488 = x_13;
x_489 = x_14;
x_490 = x_15;
goto block_510;
}
block_75:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_29 = l_Lean_Elab_Tactic_mkSimpCallStx(x_19, x_27, x_21, x_22, x_23, x_24, x_25);
lean_dec_ref(x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_23, 5);
x_33 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
lean_ctor_set(x_20, 1, x_30);
lean_ctor_set(x_20, 0, x_33);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_34);
lean_inc(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_32);
x_37 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_38 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_35, x_36, x_37, x_34, x_21, x_22, x_23, x_24, x_31);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_28);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec_ref(x_28);
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
lean_free_object(x_20);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_29, 0);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_53 = l_Lean_Elab_Tactic_mkSimpCallStx(x_19, x_51, x_21, x_22, x_23, x_24, x_25);
lean_dec_ref(x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_ctor_get(x_23, 5);
x_57 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_59);
lean_ctor_set(x_60, 4, x_59);
lean_ctor_set(x_60, 5, x_59);
lean_inc(x_56);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_62 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_63 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_60, x_61, x_62, x_59, x_21, x_22, x_23, x_24, x_55);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_52);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_52);
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_69 = x_63;
} else {
 lean_dec_ref(x_63);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_52);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
x_71 = lean_ctor_get(x_53, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_53, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_73 = x_53;
} else {
 lean_dec_ref(x_53);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
block_131:
{
lean_object* x_85; 
x_85 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_83, x_82, x_80, x_81, x_77, x_79);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7;
lean_inc(x_77);
lean_inc_ref(x_81);
lean_inc(x_80);
lean_inc_ref(x_82);
x_89 = l_Lean_Meta_simpAll(x_86, x_84, x_78, x_88, x_82, x_80, x_81, x_77, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec_ref(x_89);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_box(0);
x_95 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_94, x_83, x_82, x_80, x_81, x_77, x_92);
lean_dec(x_83);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_19 = x_76;
x_20 = x_93;
x_21 = x_82;
x_22 = x_80;
x_23 = x_81;
x_24 = x_77;
x_25 = x_96;
goto block_75;
}
else
{
uint8_t x_97; 
lean_dec(x_93);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_18);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_95);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_inc_ref(x_91);
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
lean_dec_ref(x_89);
x_102 = !lean_is_exclusive(x_90);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_90, 1);
x_104 = lean_ctor_get(x_90, 0);
lean_dec(x_104);
x_105 = lean_ctor_get(x_91, 0);
lean_inc(x_105);
lean_dec_ref(x_91);
x_106 = lean_box(0);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 1, x_106);
lean_ctor_set(x_90, 0, x_105);
x_107 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_90, x_83, x_82, x_80, x_81, x_77, x_101);
lean_dec(x_83);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec_ref(x_107);
x_19 = x_76;
x_20 = x_103;
x_21 = x_82;
x_22 = x_80;
x_23 = x_81;
x_24 = x_77;
x_25 = x_108;
goto block_75;
}
else
{
uint8_t x_109; 
lean_dec(x_103);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_18);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
return x_107;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_107);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_ctor_get(x_90, 1);
lean_inc(x_113);
lean_dec(x_90);
x_114 = lean_ctor_get(x_91, 0);
lean_inc(x_114);
lean_dec_ref(x_91);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_116, x_83, x_82, x_80, x_81, x_77, x_101);
lean_dec(x_83);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec_ref(x_117);
x_19 = x_76;
x_20 = x_113;
x_21 = x_82;
x_22 = x_80;
x_23 = x_81;
x_24 = x_77;
x_25 = x_118;
goto block_75;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_113);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_18);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
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
}
else
{
uint8_t x_123; 
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_18);
x_123 = !lean_is_exclusive(x_89);
if (x_123 == 0)
{
return x_89;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_89, 0);
x_125 = lean_ctor_get(x_89, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_89);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec(x_80);
lean_dec_ref(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_18);
x_127 = !lean_is_exclusive(x_85);
if (x_127 == 0)
{
return x_85;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_85, 0);
x_129 = lean_ctor_get(x_85, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_85);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
block_162:
{
uint8_t x_144; lean_object* x_145; lean_object* x_146; 
x_144 = 1;
x_145 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
lean_inc(x_142);
lean_inc_ref(x_141);
lean_inc(x_140);
lean_inc_ref(x_139);
lean_inc(x_136);
x_146 = l_Lean_Elab_Tactic_mkSimpContext(x_134, x_3, x_144, x_3, x_145, x_135, x_136, x_137, x_138, x_139, x_140, x_141, x_142, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc_ref(x_150);
lean_dec(x_147);
x_76 = x_134;
x_77 = x_142;
x_78 = x_150;
x_79 = x_148;
x_80 = x_140;
x_81 = x_141;
x_82 = x_139;
x_83 = x_136;
x_84 = x_149;
goto block_131;
}
else
{
lean_dec_ref(x_132);
if (x_133 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec_ref(x_146);
x_152 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_147, 1);
lean_inc_ref(x_153);
lean_dec(x_147);
x_76 = x_134;
x_77 = x_142;
x_78 = x_153;
x_79 = x_151;
x_80 = x_140;
x_81 = x_141;
x_82 = x_139;
x_83 = x_136;
x_84 = x_152;
goto block_131;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_146, 1);
lean_inc(x_154);
lean_dec_ref(x_146);
x_155 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_155);
x_156 = lean_ctor_get(x_147, 1);
lean_inc_ref(x_156);
lean_dec(x_147);
x_157 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_155);
x_76 = x_134;
x_77 = x_142;
x_78 = x_156;
x_79 = x_154;
x_80 = x_140;
x_81 = x_141;
x_82 = x_139;
x_83 = x_136;
x_84 = x_157;
goto block_131;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_18);
x_158 = !lean_is_exclusive(x_146);
if (x_158 == 0)
{
return x_146;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_146, 0);
x_160 = lean_ctor_get(x_146, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_146);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
block_186:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = l_Array_append___redArg(x_177, x_182);
lean_dec_ref(x_182);
lean_inc(x_167);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_175);
lean_ctor_set(x_184, 2, x_183);
x_185 = l_Lean_Syntax_node5(x_167, x_181, x_163, x_176, x_164, x_171, x_184);
x_132 = x_180;
x_133 = x_168;
x_134 = x_185;
x_135 = x_179;
x_136 = x_172;
x_137 = x_173;
x_138 = x_178;
x_139 = x_174;
x_140 = x_170;
x_141 = x_165;
x_142 = x_169;
x_143 = x_166;
goto block_162;
}
block_218:
{
lean_object* x_207; lean_object* x_208; 
lean_inc_ref(x_201);
x_207 = l_Array_append___redArg(x_201, x_206);
lean_dec_ref(x_206);
lean_inc(x_199);
lean_inc(x_191);
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_191);
lean_ctor_set(x_208, 1, x_199);
lean_ctor_set(x_208, 2, x_207);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_209; 
x_209 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_163 = x_187;
x_164 = x_188;
x_165 = x_189;
x_166 = x_190;
x_167 = x_191;
x_168 = x_192;
x_169 = x_193;
x_170 = x_194;
x_171 = x_208;
x_172 = x_195;
x_173 = x_196;
x_174 = x_197;
x_175 = x_199;
x_176 = x_198;
x_177 = x_201;
x_178 = x_200;
x_179 = x_202;
x_180 = x_203;
x_181 = x_204;
x_182 = x_209;
goto block_186;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_205, 0);
lean_inc(x_210);
lean_dec_ref(x_205);
x_211 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_191);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_191);
lean_ctor_set(x_212, 1, x_211);
lean_inc_ref(x_201);
x_213 = l_Array_append___redArg(x_201, x_210);
lean_dec(x_210);
lean_inc(x_199);
lean_inc(x_191);
x_214 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_214, 0, x_191);
lean_ctor_set(x_214, 1, x_199);
lean_ctor_set(x_214, 2, x_213);
x_215 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_191);
x_216 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_216, 0, x_191);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Array_mkArray3___redArg(x_212, x_214, x_216);
x_163 = x_187;
x_164 = x_188;
x_165 = x_189;
x_166 = x_190;
x_167 = x_191;
x_168 = x_192;
x_169 = x_193;
x_170 = x_194;
x_171 = x_208;
x_172 = x_195;
x_173 = x_196;
x_174 = x_197;
x_175 = x_199;
x_176 = x_198;
x_177 = x_201;
x_178 = x_200;
x_179 = x_202;
x_180 = x_203;
x_181 = x_204;
x_182 = x_217;
goto block_186;
}
}
block_247:
{
lean_object* x_239; lean_object* x_240; 
lean_inc_ref(x_233);
x_239 = l_Array_append___redArg(x_233, x_238);
lean_dec_ref(x_238);
lean_inc(x_230);
lean_inc(x_223);
x_240 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_240, 0, x_223);
lean_ctor_set(x_240, 1, x_230);
lean_ctor_set(x_240, 2, x_239);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_241; 
x_241 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_187 = x_219;
x_188 = x_240;
x_189 = x_220;
x_190 = x_222;
x_191 = x_223;
x_192 = x_224;
x_193 = x_225;
x_194 = x_226;
x_195 = x_227;
x_196 = x_228;
x_197 = x_229;
x_198 = x_231;
x_199 = x_230;
x_200 = x_232;
x_201 = x_233;
x_202 = x_234;
x_203 = x_235;
x_204 = x_236;
x_205 = x_237;
x_206 = x_241;
goto block_218;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_221, 0);
lean_inc(x_242);
lean_dec_ref(x_221);
x_243 = l_Lean_SourceInfo_fromRef(x_242, x_3);
lean_dec(x_242);
x_244 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Array_mkArray1___redArg(x_245);
x_187 = x_219;
x_188 = x_240;
x_189 = x_220;
x_190 = x_222;
x_191 = x_223;
x_192 = x_224;
x_193 = x_225;
x_194 = x_226;
x_195 = x_227;
x_196 = x_228;
x_197 = x_229;
x_198 = x_231;
x_199 = x_230;
x_200 = x_232;
x_201 = x_233;
x_202 = x_234;
x_203 = x_235;
x_204 = x_236;
x_205 = x_237;
x_206 = x_246;
goto block_218;
}
}
block_271:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = l_Array_append___redArg(x_248, x_267);
lean_dec_ref(x_267);
lean_inc(x_261);
x_269 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_269, 0, x_261);
lean_ctor_set(x_269, 1, x_250);
lean_ctor_set(x_269, 2, x_268);
x_270 = l_Lean_Syntax_node5(x_261, x_266, x_258, x_259, x_265, x_262, x_269);
x_132 = x_264;
x_133 = x_251;
x_134 = x_270;
x_135 = x_263;
x_136 = x_254;
x_137 = x_255;
x_138 = x_260;
x_139 = x_257;
x_140 = x_253;
x_141 = x_249;
x_142 = x_252;
x_143 = x_256;
goto block_162;
}
block_303:
{
lean_object* x_292; lean_object* x_293; 
lean_inc_ref(x_272);
x_292 = l_Array_append___redArg(x_272, x_291);
lean_dec_ref(x_291);
lean_inc(x_274);
lean_inc(x_286);
x_293 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_293, 0, x_286);
lean_ctor_set(x_293, 1, x_274);
lean_ctor_set(x_293, 2, x_292);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_294; 
x_294 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_248 = x_272;
x_249 = x_273;
x_250 = x_274;
x_251 = x_275;
x_252 = x_276;
x_253 = x_277;
x_254 = x_278;
x_255 = x_279;
x_256 = x_280;
x_257 = x_281;
x_258 = x_282;
x_259 = x_283;
x_260 = x_284;
x_261 = x_286;
x_262 = x_293;
x_263 = x_285;
x_264 = x_288;
x_265 = x_287;
x_266 = x_289;
x_267 = x_294;
goto block_271;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_295 = lean_ctor_get(x_290, 0);
lean_inc(x_295);
lean_dec_ref(x_290);
x_296 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_286);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_296);
lean_inc_ref(x_272);
x_298 = l_Array_append___redArg(x_272, x_295);
lean_dec(x_295);
lean_inc(x_274);
lean_inc(x_286);
x_299 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_299, 0, x_286);
lean_ctor_set(x_299, 1, x_274);
lean_ctor_set(x_299, 2, x_298);
x_300 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_286);
x_301 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_301, 0, x_286);
lean_ctor_set(x_301, 1, x_300);
x_302 = l_Array_mkArray3___redArg(x_297, x_299, x_301);
x_248 = x_272;
x_249 = x_273;
x_250 = x_274;
x_251 = x_275;
x_252 = x_276;
x_253 = x_277;
x_254 = x_278;
x_255 = x_279;
x_256 = x_280;
x_257 = x_281;
x_258 = x_282;
x_259 = x_283;
x_260 = x_284;
x_261 = x_286;
x_262 = x_293;
x_263 = x_285;
x_264 = x_288;
x_265 = x_287;
x_266 = x_289;
x_267 = x_302;
goto block_271;
}
}
block_332:
{
lean_object* x_324; lean_object* x_325; 
lean_inc_ref(x_304);
x_324 = l_Array_append___redArg(x_304, x_323);
lean_dec_ref(x_323);
lean_inc(x_307);
lean_inc(x_319);
x_325 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_325, 0, x_319);
lean_ctor_set(x_325, 1, x_307);
lean_ctor_set(x_325, 2, x_324);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_326; 
x_326 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_272 = x_304;
x_273 = x_305;
x_274 = x_307;
x_275 = x_308;
x_276 = x_309;
x_277 = x_310;
x_278 = x_311;
x_279 = x_312;
x_280 = x_313;
x_281 = x_314;
x_282 = x_315;
x_283 = x_316;
x_284 = x_317;
x_285 = x_318;
x_286 = x_319;
x_287 = x_325;
x_288 = x_320;
x_289 = x_321;
x_290 = x_322;
x_291 = x_326;
goto block_303;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_306, 0);
lean_inc(x_327);
lean_dec_ref(x_306);
x_328 = l_Lean_SourceInfo_fromRef(x_327, x_3);
lean_dec(x_327);
x_329 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
x_331 = l_Array_mkArray1___redArg(x_330);
x_272 = x_304;
x_273 = x_305;
x_274 = x_307;
x_275 = x_308;
x_276 = x_309;
x_277 = x_310;
x_278 = x_311;
x_279 = x_312;
x_280 = x_313;
x_281 = x_314;
x_282 = x_315;
x_283 = x_316;
x_284 = x_317;
x_285 = x_318;
x_286 = x_319;
x_287 = x_325;
x_288 = x_320;
x_289 = x_321;
x_290 = x_322;
x_291 = x_331;
goto block_303;
}
}
block_379:
{
lean_object* x_349; uint8_t x_350; 
x_349 = lean_st_ref_get(x_337, x_343);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_351 = lean_ctor_get(x_349, 1);
x_352 = lean_ctor_get(x_349, 0);
lean_dec(x_352);
x_353 = lean_ctor_get(x_333, 5);
x_354 = l_Lean_SourceInfo_fromRef(x_353, x_348);
x_355 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8;
x_356 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_355);
x_357 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_358 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9;
lean_ctor_set_tag(x_349, 2);
lean_ctor_set(x_349, 1, x_358);
lean_ctor_set(x_349, 0, x_357);
x_359 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_360 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_361; 
x_361 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_219 = x_349;
x_220 = x_333;
x_221 = x_335;
x_222 = x_351;
x_223 = x_354;
x_224 = x_336;
x_225 = x_337;
x_226 = x_338;
x_227 = x_339;
x_228 = x_340;
x_229 = x_341;
x_230 = x_359;
x_231 = x_342;
x_232 = x_344;
x_233 = x_360;
x_234 = x_345;
x_235 = x_346;
x_236 = x_356;
x_237 = x_347;
x_238 = x_361;
goto block_247;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_334, 0);
lean_inc(x_362);
lean_dec_ref(x_334);
x_363 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_364 = lean_array_push(x_363, x_362);
x_219 = x_349;
x_220 = x_333;
x_221 = x_335;
x_222 = x_351;
x_223 = x_354;
x_224 = x_336;
x_225 = x_337;
x_226 = x_338;
x_227 = x_339;
x_228 = x_340;
x_229 = x_341;
x_230 = x_359;
x_231 = x_342;
x_232 = x_344;
x_233 = x_360;
x_234 = x_345;
x_235 = x_346;
x_236 = x_356;
x_237 = x_347;
x_238 = x_364;
goto block_247;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_365 = lean_ctor_get(x_349, 1);
lean_inc(x_365);
lean_dec(x_349);
x_366 = lean_ctor_get(x_333, 5);
x_367 = l_Lean_SourceInfo_fromRef(x_366, x_348);
x_368 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8;
x_369 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_368);
x_370 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_371 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9;
x_372 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_374 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_375; 
x_375 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_219 = x_372;
x_220 = x_333;
x_221 = x_335;
x_222 = x_365;
x_223 = x_367;
x_224 = x_336;
x_225 = x_337;
x_226 = x_338;
x_227 = x_339;
x_228 = x_340;
x_229 = x_341;
x_230 = x_373;
x_231 = x_342;
x_232 = x_344;
x_233 = x_374;
x_234 = x_345;
x_235 = x_346;
x_236 = x_369;
x_237 = x_347;
x_238 = x_375;
goto block_247;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_334, 0);
lean_inc(x_376);
lean_dec_ref(x_334);
x_377 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_378 = lean_array_push(x_377, x_376);
x_219 = x_372;
x_220 = x_333;
x_221 = x_335;
x_222 = x_365;
x_223 = x_367;
x_224 = x_336;
x_225 = x_337;
x_226 = x_338;
x_227 = x_339;
x_228 = x_340;
x_229 = x_341;
x_230 = x_373;
x_231 = x_342;
x_232 = x_344;
x_233 = x_374;
x_234 = x_345;
x_235 = x_346;
x_236 = x_369;
x_237 = x_347;
x_238 = x_378;
goto block_247;
}
}
}
block_428:
{
if (lean_obj_tag(x_392) == 0)
{
uint8_t x_395; 
x_395 = 0;
x_333 = x_380;
x_334 = x_394;
x_335 = x_381;
x_336 = x_382;
x_337 = x_383;
x_338 = x_384;
x_339 = x_385;
x_340 = x_386;
x_341 = x_387;
x_342 = x_388;
x_343 = x_389;
x_344 = x_390;
x_345 = x_391;
x_346 = x_392;
x_347 = x_393;
x_348 = x_395;
goto block_379;
}
else
{
if (x_382 == 0)
{
x_333 = x_380;
x_334 = x_394;
x_335 = x_381;
x_336 = x_382;
x_337 = x_383;
x_338 = x_384;
x_339 = x_385;
x_340 = x_386;
x_341 = x_387;
x_342 = x_388;
x_343 = x_389;
x_344 = x_390;
x_345 = x_391;
x_346 = x_392;
x_347 = x_393;
x_348 = x_382;
goto block_379;
}
else
{
lean_object* x_396; uint8_t x_397; 
x_396 = lean_st_ref_get(x_383, x_389);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_398 = lean_ctor_get(x_396, 1);
x_399 = lean_ctor_get(x_396, 0);
lean_dec(x_399);
x_400 = lean_ctor_get(x_380, 5);
x_401 = 0;
x_402 = l_Lean_SourceInfo_fromRef(x_400, x_401);
x_403 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10;
x_404 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_403);
x_405 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_406 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11;
lean_ctor_set_tag(x_396, 2);
lean_ctor_set(x_396, 1, x_406);
lean_ctor_set(x_396, 0, x_405);
x_407 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_408 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_409; 
x_409 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_304 = x_408;
x_305 = x_380;
x_306 = x_381;
x_307 = x_407;
x_308 = x_382;
x_309 = x_383;
x_310 = x_384;
x_311 = x_385;
x_312 = x_386;
x_313 = x_398;
x_314 = x_387;
x_315 = x_396;
x_316 = x_388;
x_317 = x_390;
x_318 = x_391;
x_319 = x_402;
x_320 = x_392;
x_321 = x_404;
x_322 = x_393;
x_323 = x_409;
goto block_332;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_394, 0);
lean_inc(x_410);
lean_dec_ref(x_394);
x_411 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_412 = lean_array_push(x_411, x_410);
x_304 = x_408;
x_305 = x_380;
x_306 = x_381;
x_307 = x_407;
x_308 = x_382;
x_309 = x_383;
x_310 = x_384;
x_311 = x_385;
x_312 = x_386;
x_313 = x_398;
x_314 = x_387;
x_315 = x_396;
x_316 = x_388;
x_317 = x_390;
x_318 = x_391;
x_319 = x_402;
x_320 = x_392;
x_321 = x_404;
x_322 = x_393;
x_323 = x_412;
goto block_332;
}
}
else
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_413 = lean_ctor_get(x_396, 1);
lean_inc(x_413);
lean_dec(x_396);
x_414 = lean_ctor_get(x_380, 5);
x_415 = 0;
x_416 = l_Lean_SourceInfo_fromRef(x_414, x_415);
x_417 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10;
x_418 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_417);
x_419 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_420 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11;
x_421 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_423 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_424; 
x_424 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_304 = x_423;
x_305 = x_380;
x_306 = x_381;
x_307 = x_422;
x_308 = x_382;
x_309 = x_383;
x_310 = x_384;
x_311 = x_385;
x_312 = x_386;
x_313 = x_413;
x_314 = x_387;
x_315 = x_421;
x_316 = x_388;
x_317 = x_390;
x_318 = x_391;
x_319 = x_416;
x_320 = x_392;
x_321 = x_418;
x_322 = x_393;
x_323 = x_424;
goto block_332;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_394, 0);
lean_inc(x_425);
lean_dec_ref(x_394);
x_426 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_427 = lean_array_push(x_426, x_425);
x_304 = x_423;
x_305 = x_380;
x_306 = x_381;
x_307 = x_422;
x_308 = x_382;
x_309 = x_383;
x_310 = x_384;
x_311 = x_385;
x_312 = x_386;
x_313 = x_413;
x_314 = x_387;
x_315 = x_421;
x_316 = x_388;
x_317 = x_390;
x_318 = x_391;
x_319 = x_416;
x_320 = x_392;
x_321 = x_418;
x_322 = x_393;
x_323 = x_427;
goto block_332;
}
}
}
}
}
block_449:
{
lean_object* x_444; 
x_444 = l_Lean_Syntax_getOptional_x3f(x_430);
lean_dec(x_430);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; 
x_445 = lean_box(0);
x_380 = x_441;
x_381 = x_431;
x_382 = x_433;
x_383 = x_442;
x_384 = x_440;
x_385 = x_436;
x_386 = x_437;
x_387 = x_439;
x_388 = x_429;
x_389 = x_443;
x_390 = x_438;
x_391 = x_435;
x_392 = x_432;
x_393 = x_434;
x_394 = x_445;
goto block_428;
}
else
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_444);
if (x_446 == 0)
{
x_380 = x_441;
x_381 = x_431;
x_382 = x_433;
x_383 = x_442;
x_384 = x_440;
x_385 = x_436;
x_386 = x_437;
x_387 = x_439;
x_388 = x_429;
x_389 = x_443;
x_390 = x_438;
x_391 = x_435;
x_392 = x_432;
x_393 = x_434;
x_394 = x_444;
goto block_428;
}
else
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_444, 0);
lean_inc(x_447);
lean_dec(x_444);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
x_380 = x_441;
x_381 = x_431;
x_382 = x_433;
x_383 = x_442;
x_384 = x_440;
x_385 = x_436;
x_386 = x_437;
x_387 = x_439;
x_388 = x_429;
x_389 = x_443;
x_390 = x_438;
x_391 = x_435;
x_392 = x_432;
x_393 = x_434;
x_394 = x_448;
goto block_428;
}
}
}
block_480:
{
lean_object* x_466; lean_object* x_467; uint8_t x_468; 
x_466 = lean_unsigned_to_nat(3u);
x_467 = l_Lean_Syntax_getArg(x_455, x_466);
lean_dec(x_455);
x_468 = l_Lean_Syntax_isNone(x_467);
if (x_468 == 0)
{
uint8_t x_469; 
lean_inc(x_467);
x_469 = l_Lean_Syntax_matchesNull(x_467, x_450);
if (x_469 == 0)
{
lean_object* x_470; 
lean_dec(x_467);
lean_dec(x_464);
lean_dec_ref(x_463);
lean_dec(x_462);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec_ref(x_459);
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_470 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_465);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_471 = l_Lean_Syntax_getArg(x_467, x_17);
lean_dec(x_467);
x_472 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_473 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_472);
lean_inc(x_471);
x_474 = l_Lean_Syntax_isOfKind(x_471, x_473);
lean_dec(x_473);
if (x_474 == 0)
{
lean_object* x_475; 
lean_dec(x_471);
lean_dec(x_464);
lean_dec_ref(x_463);
lean_dec(x_462);
lean_dec_ref(x_461);
lean_dec(x_460);
lean_dec_ref(x_459);
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_475 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_465);
return x_475;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = l_Lean_Syntax_getArg(x_471, x_450);
lean_dec(x_471);
x_477 = l_Lean_Syntax_getArgs(x_476);
lean_dec(x_476);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
x_429 = x_451;
x_430 = x_452;
x_431 = x_456;
x_432 = x_453;
x_433 = x_454;
x_434 = x_478;
x_435 = x_457;
x_436 = x_458;
x_437 = x_459;
x_438 = x_460;
x_439 = x_461;
x_440 = x_462;
x_441 = x_463;
x_442 = x_464;
x_443 = x_465;
goto block_449;
}
}
}
else
{
lean_object* x_479; 
lean_dec(x_467);
x_479 = lean_box(0);
x_429 = x_451;
x_430 = x_452;
x_431 = x_456;
x_432 = x_453;
x_433 = x_454;
x_434 = x_479;
x_435 = x_457;
x_436 = x_458;
x_437 = x_459;
x_438 = x_460;
x_439 = x_461;
x_440 = x_462;
x_441 = x_463;
x_442 = x_464;
x_443 = x_465;
goto block_449;
}
}
block_510:
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_491 = lean_unsigned_to_nat(2u);
x_492 = l_Lean_Syntax_getArg(x_2, x_491);
x_493 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__13;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_494 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_493);
lean_inc(x_492);
x_495 = l_Lean_Syntax_isOfKind(x_492, x_494);
lean_dec(x_494);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_492);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec_ref(x_486);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_496 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_490);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_497 = l_Lean_Syntax_getArg(x_492, x_17);
x_498 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_499 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_498);
lean_inc(x_497);
x_500 = l_Lean_Syntax_isOfKind(x_497, x_499);
lean_dec(x_499);
if (x_500 == 0)
{
lean_object* x_501; 
lean_dec(x_497);
lean_dec(x_492);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec_ref(x_486);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_501 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_490);
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; uint8_t x_504; 
x_502 = l_Lean_Syntax_getArg(x_492, x_450);
x_503 = l_Lean_Syntax_getArg(x_492, x_491);
x_504 = l_Lean_Syntax_isNone(x_503);
if (x_504 == 0)
{
uint8_t x_505; 
lean_inc(x_503);
x_505 = l_Lean_Syntax_matchesNull(x_503, x_450);
if (x_505 == 0)
{
lean_object* x_506; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_497);
lean_dec(x_492);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec_ref(x_486);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_506 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_490);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; 
x_507 = l_Lean_Syntax_getArg(x_503, x_17);
lean_dec(x_503);
x_508 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_508, 0, x_507);
x_451 = x_497;
x_452 = x_502;
x_453 = x_481;
x_454 = x_500;
x_455 = x_492;
x_456 = x_508;
x_457 = x_482;
x_458 = x_483;
x_459 = x_484;
x_460 = x_485;
x_461 = x_486;
x_462 = x_487;
x_463 = x_488;
x_464 = x_489;
x_465 = x_490;
goto block_480;
}
}
else
{
lean_object* x_509; 
lean_dec(x_503);
x_509 = lean_box(0);
x_451 = x_497;
x_452 = x_502;
x_453 = x_481;
x_454 = x_500;
x_455 = x_492;
x_456 = x_509;
x_457 = x_482;
x_458 = x_483;
x_459 = x_484;
x_460 = x_485;
x_461 = x_486;
x_462 = x_487;
x_463 = x_488;
x_464 = x_489;
x_465 = x_490;
goto block_480;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAllTrace", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_12 = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_13 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_14 = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
x_16 = 1;
x_17 = lean_box(x_15);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___boxed), 15, 6);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_11);
lean_closure_set(x_19, 4, x_12);
lean_closure_set(x_19, 5, x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = l_Lean_Elab_Tactic_withMainContext___redArg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
x_17 = lean_unbox(x_3);
x_18 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0(x_16, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpAllTrace", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_3 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(51u);
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(35u);
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5;
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1;
x_3 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l_Lean_Meta_dsimpGoal(x_12, x_1, x_2, x_4, x_3, x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_20, x_5, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_19);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_19);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_inc_ref(x_17);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec_ref(x_15);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec_ref(x_17);
x_35 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_35);
lean_ctor_set(x_16, 0, x_34);
x_36 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_16, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_32);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_32);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_ctor_get(x_17, 0);
lean_inc(x_46);
lean_dec_ref(x_17);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_48, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
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
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
return x_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_15);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_11);
if (x_61 == 0)
{
return x_11;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_11, 0);
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_11);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_4, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_15 = l_Lean_MVarId_getNondepPropHyps(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = 1;
x_19 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(x_1, x_2, x_16, x_18, x_4, x_7, x_8, x_9, x_10, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_6);
x_14 = l_Lean_Elab_Tactic_getFVarIds(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_dsimpLocation_x27_go___redArg(x_2, x_3, x_15, x_4, x_6, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_6);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed), 11, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Tactic_withMainContext___redArg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_dec_ref(x_3);
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed), 13, 4);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_Elab_Tactic_withMainContext___redArg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_x27___lam__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimp", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpAutoUnfold", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimp!", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpTraceArgsRest", 18, 18);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (x_1 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_506; uint8_t x_507; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_447 = lean_unsigned_to_nat(1u);
x_506 = l_Lean_Syntax_getArg(x_2, x_447);
x_507 = l_Lean_Syntax_isNone(x_506);
if (x_507 == 0)
{
uint8_t x_508; 
lean_inc(x_506);
x_508 = l_Lean_Syntax_matchesNull(x_506, x_447);
if (x_508 == 0)
{
lean_object* x_509; 
lean_dec(x_506);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_509 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_15);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; 
x_510 = l_Lean_Syntax_getArg(x_506, x_17);
lean_dec(x_506);
x_511 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_511, 0, x_510);
x_477 = x_511;
x_478 = x_7;
x_479 = x_8;
x_480 = x_9;
x_481 = x_10;
x_482 = x_11;
x_483 = x_12;
x_484 = x_13;
x_485 = x_14;
x_486 = x_15;
goto block_505;
}
}
else
{
lean_object* x_512; 
lean_dec(x_506);
x_512 = lean_box(0);
x_477 = x_512;
x_478 = x_7;
x_479 = x_8;
x_480 = x_9;
x_481 = x_10;
x_482 = x_11;
x_483 = x_12;
x_484 = x_13;
x_485 = x_14;
x_486 = x_15;
goto block_505;
}
block_88:
{
lean_object* x_32; 
lean_inc(x_26);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_27);
x_32 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_30, x_29, x_31, x_20, x_25, x_23, x_19, x_27, x_21, x_22, x_26, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_26);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_27);
x_38 = l_Lean_Elab_Tactic_mkSimpCallStx(x_24, x_36, x_27, x_21, x_22, x_26, x_34);
lean_dec_ref(x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_22, 5);
x_42 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
lean_ctor_set(x_33, 1, x_39);
lean_ctor_set(x_33, 0, x_42);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_43);
lean_inc(x_41);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_41);
x_46 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_47 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_44, x_45, x_46, x_43, x_27, x_21, x_22, x_26, x_40);
lean_dec(x_21);
lean_dec_ref(x_27);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_37);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_37);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_37);
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
uint8_t x_56; 
lean_free_object(x_33);
lean_dec_ref(x_37);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_33, 0);
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_33);
lean_inc(x_26);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_27);
x_62 = l_Lean_Elab_Tactic_mkSimpCallStx(x_24, x_60, x_27, x_21, x_22, x_26, x_34);
lean_dec_ref(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_ctor_get(x_22, 5);
x_66 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_68);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set(x_69, 5, x_68);
lean_inc(x_65);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_71 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_72 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_69, x_70, x_71, x_68, x_27, x_21, x_22, x_26, x_64);
lean_dec(x_21);
lean_dec_ref(x_27);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_61);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_61);
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
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
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_61);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
x_80 = lean_ctor_get(x_62, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_62, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_82 = x_62;
} else {
 lean_dec_ref(x_62);
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
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_18);
x_84 = !lean_is_exclusive(x_32);
if (x_84 == 0)
{
return x_32;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_32, 0);
x_86 = lean_ctor_get(x_32, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_32);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
block_106:
{
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0;
x_103 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_3);
x_19 = x_89;
x_20 = x_90;
x_21 = x_91;
x_22 = x_93;
x_23 = x_92;
x_24 = x_94;
x_25 = x_95;
x_26 = x_96;
x_27 = x_97;
x_28 = x_99;
x_29 = x_100;
x_30 = x_101;
x_31 = x_103;
goto block_88;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
lean_dec_ref(x_98);
x_105 = l_Lean_Elab_Tactic_expandLocation(x_104);
lean_dec(x_104);
x_19 = x_89;
x_20 = x_90;
x_21 = x_91;
x_22 = x_93;
x_23 = x_92;
x_24 = x_94;
x_25 = x_95;
x_26 = x_96;
x_27 = x_97;
x_28 = x_99;
x_29 = x_100;
x_30 = x_101;
x_31 = x_105;
goto block_88;
}
}
block_143:
{
uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = 0;
x_121 = 2;
x_122 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
x_123 = lean_box(x_120);
x_124 = lean_box(x_121);
x_125 = lean_box(x_120);
lean_inc(x_110);
x_126 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_126, 0, x_110);
lean_closure_set(x_126, 1, x_123);
lean_closure_set(x_126, 2, x_124);
lean_closure_set(x_126, 3, x_125);
lean_closure_set(x_126, 4, x_122);
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
x_127 = l_Lean_Elab_Tactic_withMainContext___redArg(x_126, x_111, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc_ref(x_131);
lean_dec(x_128);
x_89 = x_114;
x_90 = x_111;
x_91 = x_116;
x_92 = x_113;
x_93 = x_117;
x_94 = x_110;
x_95 = x_112;
x_96 = x_118;
x_97 = x_115;
x_98 = x_108;
x_99 = x_129;
x_100 = x_131;
x_101 = x_130;
goto block_106;
}
else
{
lean_dec_ref(x_109);
if (x_107 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec_ref(x_127);
x_133 = lean_ctor_get(x_128, 0);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_128, 1);
lean_inc_ref(x_134);
lean_dec(x_128);
x_89 = x_114;
x_90 = x_111;
x_91 = x_116;
x_92 = x_113;
x_93 = x_117;
x_94 = x_110;
x_95 = x_112;
x_96 = x_118;
x_97 = x_115;
x_98 = x_108;
x_99 = x_132;
x_100 = x_134;
x_101 = x_133;
goto block_106;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_127, 1);
lean_inc(x_135);
lean_dec_ref(x_127);
x_136 = lean_ctor_get(x_128, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_128, 1);
lean_inc_ref(x_137);
lean_dec(x_128);
x_138 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_136);
x_89 = x_114;
x_90 = x_111;
x_91 = x_116;
x_92 = x_113;
x_93 = x_117;
x_94 = x_110;
x_95 = x_112;
x_96 = x_118;
x_97 = x_115;
x_98 = x_108;
x_99 = x_135;
x_100 = x_137;
x_101 = x_138;
goto block_106;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_18);
x_139 = !lean_is_exclusive(x_127);
if (x_139 == 0)
{
return x_127;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_127, 0);
x_141 = lean_ctor_get(x_127, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_127);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
block_169:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = l_Array_append___redArg(x_154, x_165);
lean_dec_ref(x_165);
lean_inc(x_150);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_150);
lean_ctor_set(x_167, 1, x_155);
lean_ctor_set(x_167, 2, x_166);
x_168 = l_Lean_Syntax_node6(x_150, x_152, x_147, x_156, x_158, x_148, x_164, x_167);
x_107 = x_144;
x_108 = x_162;
x_109 = x_151;
x_110 = x_168;
x_111 = x_146;
x_112 = x_163;
x_113 = x_160;
x_114 = x_149;
x_115 = x_161;
x_116 = x_145;
x_117 = x_153;
x_118 = x_159;
x_119 = x_157;
goto block_143;
}
block_197:
{
lean_object* x_191; lean_object* x_192; 
lean_inc_ref(x_180);
x_191 = l_Array_append___redArg(x_180, x_190);
lean_dec_ref(x_190);
lean_inc(x_181);
lean_inc(x_176);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_176);
lean_ctor_set(x_192, 1, x_181);
lean_ctor_set(x_192, 2, x_191);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_193; 
x_193 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_144 = x_170;
x_145 = x_171;
x_146 = x_172;
x_147 = x_173;
x_148 = x_174;
x_149 = x_175;
x_150 = x_176;
x_151 = x_177;
x_152 = x_178;
x_153 = x_179;
x_154 = x_180;
x_155 = x_181;
x_156 = x_182;
x_157 = x_184;
x_158 = x_183;
x_159 = x_185;
x_160 = x_186;
x_161 = x_187;
x_162 = x_188;
x_163 = x_189;
x_164 = x_192;
x_165 = x_193;
goto block_169;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_188, 0);
x_195 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
lean_inc(x_194);
x_196 = lean_array_push(x_195, x_194);
x_144 = x_170;
x_145 = x_171;
x_146 = x_172;
x_147 = x_173;
x_148 = x_174;
x_149 = x_175;
x_150 = x_176;
x_151 = x_177;
x_152 = x_178;
x_153 = x_179;
x_154 = x_180;
x_155 = x_181;
x_156 = x_182;
x_157 = x_184;
x_158 = x_183;
x_159 = x_185;
x_160 = x_186;
x_161 = x_187;
x_162 = x_188;
x_163 = x_189;
x_164 = x_192;
x_165 = x_196;
goto block_169;
}
}
block_230:
{
lean_object* x_219; lean_object* x_220; 
lean_inc_ref(x_207);
x_219 = l_Array_append___redArg(x_207, x_218);
lean_dec_ref(x_218);
lean_inc(x_208);
lean_inc(x_203);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_203);
lean_ctor_set(x_220, 1, x_208);
lean_ctor_set(x_220, 2, x_219);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_221; 
x_221 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_170 = x_198;
x_171 = x_199;
x_172 = x_200;
x_173 = x_201;
x_174 = x_220;
x_175 = x_202;
x_176 = x_203;
x_177 = x_204;
x_178 = x_205;
x_179 = x_206;
x_180 = x_207;
x_181 = x_208;
x_182 = x_209;
x_183 = x_211;
x_184 = x_210;
x_185 = x_212;
x_186 = x_213;
x_187 = x_214;
x_188 = x_216;
x_189 = x_217;
x_190 = x_221;
goto block_197;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_215, 0);
lean_inc(x_222);
lean_dec_ref(x_215);
x_223 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_203);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_203);
lean_ctor_set(x_224, 1, x_223);
lean_inc_ref(x_207);
x_225 = l_Array_append___redArg(x_207, x_222);
lean_dec(x_222);
lean_inc(x_208);
lean_inc(x_203);
x_226 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_226, 0, x_203);
lean_ctor_set(x_226, 1, x_208);
lean_ctor_set(x_226, 2, x_225);
x_227 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_203);
x_228 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_228, 0, x_203);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Array_mkArray3___redArg(x_224, x_226, x_228);
x_170 = x_198;
x_171 = x_199;
x_172 = x_200;
x_173 = x_201;
x_174 = x_220;
x_175 = x_202;
x_176 = x_203;
x_177 = x_204;
x_178 = x_205;
x_179 = x_206;
x_180 = x_207;
x_181 = x_208;
x_182 = x_209;
x_183 = x_211;
x_184 = x_210;
x_185 = x_212;
x_186 = x_213;
x_187 = x_214;
x_188 = x_216;
x_189 = x_217;
x_190 = x_229;
goto block_197;
}
}
block_256:
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = l_Array_append___redArg(x_244, x_252);
lean_dec_ref(x_252);
lean_inc(x_231);
x_254 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_254, 0, x_231);
lean_ctor_set(x_254, 1, x_233);
lean_ctor_set(x_254, 2, x_253);
x_255 = l_Lean_Syntax_node6(x_231, x_248, x_240, x_241, x_242, x_249, x_246, x_254);
x_107 = x_232;
x_108 = x_250;
x_109 = x_238;
x_110 = x_255;
x_111 = x_235;
x_112 = x_251;
x_113 = x_245;
x_114 = x_237;
x_115 = x_247;
x_116 = x_234;
x_117 = x_239;
x_118 = x_243;
x_119 = x_236;
goto block_143;
}
block_284:
{
lean_object* x_278; lean_object* x_279; 
lean_inc_ref(x_270);
x_278 = l_Array_append___redArg(x_270, x_277);
lean_dec_ref(x_277);
lean_inc(x_258);
lean_inc(x_257);
x_279 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_279, 0, x_257);
lean_ctor_set(x_279, 1, x_258);
lean_ctor_set(x_279, 2, x_278);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_280; 
x_280 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_231 = x_257;
x_232 = x_259;
x_233 = x_258;
x_234 = x_260;
x_235 = x_261;
x_236 = x_262;
x_237 = x_263;
x_238 = x_264;
x_239 = x_265;
x_240 = x_266;
x_241 = x_267;
x_242 = x_268;
x_243 = x_269;
x_244 = x_270;
x_245 = x_271;
x_246 = x_279;
x_247 = x_274;
x_248 = x_273;
x_249 = x_272;
x_250 = x_275;
x_251 = x_276;
x_252 = x_280;
goto block_256;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_275, 0);
x_282 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
lean_inc(x_281);
x_283 = lean_array_push(x_282, x_281);
x_231 = x_257;
x_232 = x_259;
x_233 = x_258;
x_234 = x_260;
x_235 = x_261;
x_236 = x_262;
x_237 = x_263;
x_238 = x_264;
x_239 = x_265;
x_240 = x_266;
x_241 = x_267;
x_242 = x_268;
x_243 = x_269;
x_244 = x_270;
x_245 = x_271;
x_246 = x_279;
x_247 = x_274;
x_248 = x_273;
x_249 = x_272;
x_250 = x_275;
x_251 = x_276;
x_252 = x_283;
goto block_256;
}
}
block_317:
{
lean_object* x_306; lean_object* x_307; 
lean_inc_ref(x_298);
x_306 = l_Array_append___redArg(x_298, x_305);
lean_dec_ref(x_305);
lean_inc(x_286);
lean_inc(x_285);
x_307 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_307, 0, x_285);
lean_ctor_set(x_307, 1, x_286);
lean_ctor_set(x_307, 2, x_306);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_308; 
x_308 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_257 = x_285;
x_258 = x_286;
x_259 = x_287;
x_260 = x_288;
x_261 = x_289;
x_262 = x_290;
x_263 = x_291;
x_264 = x_292;
x_265 = x_293;
x_266 = x_294;
x_267 = x_295;
x_268 = x_296;
x_269 = x_297;
x_270 = x_298;
x_271 = x_299;
x_272 = x_307;
x_273 = x_301;
x_274 = x_300;
x_275 = x_303;
x_276 = x_304;
x_277 = x_308;
goto block_284;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_309 = lean_ctor_get(x_302, 0);
lean_inc(x_309);
lean_dec_ref(x_302);
x_310 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_285);
x_311 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_311, 0, x_285);
lean_ctor_set(x_311, 1, x_310);
lean_inc_ref(x_298);
x_312 = l_Array_append___redArg(x_298, x_309);
lean_dec(x_309);
lean_inc(x_286);
lean_inc(x_285);
x_313 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_313, 0, x_285);
lean_ctor_set(x_313, 1, x_286);
lean_ctor_set(x_313, 2, x_312);
x_314 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_285);
x_315 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_315, 0, x_285);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Array_mkArray3___redArg(x_311, x_313, x_315);
x_257 = x_285;
x_258 = x_286;
x_259 = x_287;
x_260 = x_288;
x_261 = x_289;
x_262 = x_290;
x_263 = x_291;
x_264 = x_292;
x_265 = x_293;
x_266 = x_294;
x_267 = x_295;
x_268 = x_296;
x_269 = x_297;
x_270 = x_298;
x_271 = x_299;
x_272 = x_307;
x_273 = x_301;
x_274 = x_300;
x_275 = x_303;
x_276 = x_304;
x_277 = x_316;
goto block_284;
}
}
block_368:
{
lean_object* x_334; uint8_t x_335; 
x_334 = lean_st_ref_get(x_327, x_319);
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_336 = lean_ctor_get(x_334, 1);
x_337 = lean_ctor_get(x_334, 0);
lean_dec(x_337);
x_338 = lean_ctor_get(x_325, 5);
x_339 = l_Lean_SourceInfo_fromRef(x_338, x_333);
x_340 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1;
x_341 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_340);
x_342 = l_Lean_SourceInfo_fromRef(x_18, x_3);
lean_ctor_set_tag(x_334, 2);
lean_ctor_set(x_334, 1, x_340);
lean_ctor_set(x_334, 0, x_342);
x_343 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_344 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
lean_inc(x_339);
x_345 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_345, 0, x_339);
lean_ctor_set(x_345, 1, x_343);
lean_ctor_set(x_345, 2, x_344);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_346; 
x_346 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_198 = x_318;
x_199 = x_320;
x_200 = x_321;
x_201 = x_334;
x_202 = x_323;
x_203 = x_339;
x_204 = x_324;
x_205 = x_341;
x_206 = x_325;
x_207 = x_344;
x_208 = x_343;
x_209 = x_326;
x_210 = x_336;
x_211 = x_345;
x_212 = x_327;
x_213 = x_328;
x_214 = x_329;
x_215 = x_330;
x_216 = x_331;
x_217 = x_332;
x_218 = x_346;
goto block_230;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_347 = lean_ctor_get(x_322, 0);
lean_inc(x_347);
lean_dec_ref(x_322);
x_348 = l_Lean_SourceInfo_fromRef(x_347, x_3);
lean_dec(x_347);
x_349 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_350 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Array_mkArray1___redArg(x_350);
x_198 = x_318;
x_199 = x_320;
x_200 = x_321;
x_201 = x_334;
x_202 = x_323;
x_203 = x_339;
x_204 = x_324;
x_205 = x_341;
x_206 = x_325;
x_207 = x_344;
x_208 = x_343;
x_209 = x_326;
x_210 = x_336;
x_211 = x_345;
x_212 = x_327;
x_213 = x_328;
x_214 = x_329;
x_215 = x_330;
x_216 = x_331;
x_217 = x_332;
x_218 = x_351;
goto block_230;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_352 = lean_ctor_get(x_334, 1);
lean_inc(x_352);
lean_dec(x_334);
x_353 = lean_ctor_get(x_325, 5);
x_354 = l_Lean_SourceInfo_fromRef(x_353, x_333);
x_355 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1;
x_356 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_355);
x_357 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_358 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_355);
x_359 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_360 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
lean_inc(x_354);
x_361 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_361, 0, x_354);
lean_ctor_set(x_361, 1, x_359);
lean_ctor_set(x_361, 2, x_360);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_362; 
x_362 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_198 = x_318;
x_199 = x_320;
x_200 = x_321;
x_201 = x_358;
x_202 = x_323;
x_203 = x_354;
x_204 = x_324;
x_205 = x_356;
x_206 = x_325;
x_207 = x_360;
x_208 = x_359;
x_209 = x_326;
x_210 = x_352;
x_211 = x_361;
x_212 = x_327;
x_213 = x_328;
x_214 = x_329;
x_215 = x_330;
x_216 = x_331;
x_217 = x_332;
x_218 = x_362;
goto block_230;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_363 = lean_ctor_get(x_322, 0);
lean_inc(x_363);
lean_dec_ref(x_322);
x_364 = l_Lean_SourceInfo_fromRef(x_363, x_3);
lean_dec(x_363);
x_365 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_366 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Array_mkArray1___redArg(x_366);
x_198 = x_318;
x_199 = x_320;
x_200 = x_321;
x_201 = x_358;
x_202 = x_323;
x_203 = x_354;
x_204 = x_324;
x_205 = x_356;
x_206 = x_325;
x_207 = x_360;
x_208 = x_359;
x_209 = x_326;
x_210 = x_352;
x_211 = x_361;
x_212 = x_327;
x_213 = x_328;
x_214 = x_329;
x_215 = x_330;
x_216 = x_331;
x_217 = x_332;
x_218 = x_367;
goto block_230;
}
}
}
block_423:
{
if (lean_obj_tag(x_375) == 0)
{
uint8_t x_384; 
x_384 = 0;
x_318 = x_369;
x_319 = x_370;
x_320 = x_371;
x_321 = x_372;
x_322 = x_373;
x_323 = x_374;
x_324 = x_375;
x_325 = x_376;
x_326 = x_377;
x_327 = x_378;
x_328 = x_379;
x_329 = x_380;
x_330 = x_381;
x_331 = x_383;
x_332 = x_382;
x_333 = x_384;
goto block_368;
}
else
{
if (x_369 == 0)
{
x_318 = x_369;
x_319 = x_370;
x_320 = x_371;
x_321 = x_372;
x_322 = x_373;
x_323 = x_374;
x_324 = x_375;
x_325 = x_376;
x_326 = x_377;
x_327 = x_378;
x_328 = x_379;
x_329 = x_380;
x_330 = x_381;
x_331 = x_383;
x_332 = x_382;
x_333 = x_369;
goto block_368;
}
else
{
lean_object* x_385; uint8_t x_386; 
x_385 = lean_st_ref_get(x_378, x_370);
x_386 = !lean_is_exclusive(x_385);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_387 = lean_ctor_get(x_385, 1);
x_388 = lean_ctor_get(x_385, 0);
lean_dec(x_388);
x_389 = lean_ctor_get(x_376, 5);
x_390 = 0;
x_391 = l_Lean_SourceInfo_fromRef(x_389, x_390);
x_392 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2;
x_393 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_392);
x_394 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_395 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3;
lean_ctor_set_tag(x_385, 2);
lean_ctor_set(x_385, 1, x_395);
lean_ctor_set(x_385, 0, x_394);
x_396 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_397 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
lean_inc(x_391);
x_398 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_398, 0, x_391);
lean_ctor_set(x_398, 1, x_396);
lean_ctor_set(x_398, 2, x_397);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_399; 
x_399 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_285 = x_391;
x_286 = x_396;
x_287 = x_369;
x_288 = x_371;
x_289 = x_372;
x_290 = x_387;
x_291 = x_374;
x_292 = x_375;
x_293 = x_376;
x_294 = x_385;
x_295 = x_377;
x_296 = x_398;
x_297 = x_378;
x_298 = x_397;
x_299 = x_379;
x_300 = x_380;
x_301 = x_393;
x_302 = x_381;
x_303 = x_383;
x_304 = x_382;
x_305 = x_399;
goto block_317;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_400 = lean_ctor_get(x_373, 0);
lean_inc(x_400);
lean_dec_ref(x_373);
x_401 = l_Lean_SourceInfo_fromRef(x_400, x_3);
lean_dec(x_400);
x_402 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_403 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_Array_mkArray1___redArg(x_403);
x_285 = x_391;
x_286 = x_396;
x_287 = x_369;
x_288 = x_371;
x_289 = x_372;
x_290 = x_387;
x_291 = x_374;
x_292 = x_375;
x_293 = x_376;
x_294 = x_385;
x_295 = x_377;
x_296 = x_398;
x_297 = x_378;
x_298 = x_397;
x_299 = x_379;
x_300 = x_380;
x_301 = x_393;
x_302 = x_381;
x_303 = x_383;
x_304 = x_382;
x_305 = x_404;
goto block_317;
}
}
else
{
lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_405 = lean_ctor_get(x_385, 1);
lean_inc(x_405);
lean_dec(x_385);
x_406 = lean_ctor_get(x_376, 5);
x_407 = 0;
x_408 = l_Lean_SourceInfo_fromRef(x_406, x_407);
x_409 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2;
x_410 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_409);
x_411 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_412 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3;
x_413 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_414 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_415 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
lean_inc(x_408);
x_416 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_416, 0, x_408);
lean_ctor_set(x_416, 1, x_414);
lean_ctor_set(x_416, 2, x_415);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_417; 
x_417 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_285 = x_408;
x_286 = x_414;
x_287 = x_369;
x_288 = x_371;
x_289 = x_372;
x_290 = x_405;
x_291 = x_374;
x_292 = x_375;
x_293 = x_376;
x_294 = x_413;
x_295 = x_377;
x_296 = x_416;
x_297 = x_378;
x_298 = x_415;
x_299 = x_379;
x_300 = x_380;
x_301 = x_410;
x_302 = x_381;
x_303 = x_383;
x_304 = x_382;
x_305 = x_417;
goto block_317;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_373, 0);
lean_inc(x_418);
lean_dec_ref(x_373);
x_419 = l_Lean_SourceInfo_fromRef(x_418, x_3);
lean_dec(x_418);
x_420 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_421 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = l_Array_mkArray1___redArg(x_421);
x_285 = x_408;
x_286 = x_414;
x_287 = x_369;
x_288 = x_371;
x_289 = x_372;
x_290 = x_405;
x_291 = x_374;
x_292 = x_375;
x_293 = x_376;
x_294 = x_413;
x_295 = x_377;
x_296 = x_416;
x_297 = x_378;
x_298 = x_415;
x_299 = x_379;
x_300 = x_380;
x_301 = x_410;
x_302 = x_381;
x_303 = x_383;
x_304 = x_382;
x_305 = x_422;
goto block_317;
}
}
}
}
}
block_446:
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_unsigned_to_nat(3u);
x_440 = l_Lean_Syntax_getArg(x_427, x_439);
lean_dec(x_427);
x_441 = l_Lean_Syntax_getOptional_x3f(x_440);
lean_dec(x_440);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; 
x_442 = lean_box(0);
x_369 = x_424;
x_370 = x_438;
x_371 = x_435;
x_372 = x_430;
x_373 = x_426;
x_374 = x_433;
x_375 = x_428;
x_376 = x_436;
x_377 = x_425;
x_378 = x_437;
x_379 = x_432;
x_380 = x_434;
x_381 = x_429;
x_382 = x_431;
x_383 = x_442;
goto block_423;
}
else
{
uint8_t x_443; 
x_443 = !lean_is_exclusive(x_441);
if (x_443 == 0)
{
x_369 = x_424;
x_370 = x_438;
x_371 = x_435;
x_372 = x_430;
x_373 = x_426;
x_374 = x_433;
x_375 = x_428;
x_376 = x_436;
x_377 = x_425;
x_378 = x_437;
x_379 = x_432;
x_380 = x_434;
x_381 = x_429;
x_382 = x_431;
x_383 = x_441;
goto block_423;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_441, 0);
lean_inc(x_444);
lean_dec(x_441);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
x_369 = x_424;
x_370 = x_438;
x_371 = x_435;
x_372 = x_430;
x_373 = x_426;
x_374 = x_433;
x_375 = x_428;
x_376 = x_436;
x_377 = x_425;
x_378 = x_437;
x_379 = x_432;
x_380 = x_434;
x_381 = x_429;
x_382 = x_431;
x_383 = x_445;
goto block_423;
}
}
}
block_476:
{
lean_object* x_463; uint8_t x_464; 
x_463 = l_Lean_Syntax_getArg(x_452, x_450);
x_464 = l_Lean_Syntax_isNone(x_463);
if (x_464 == 0)
{
uint8_t x_465; 
lean_inc(x_463);
x_465 = l_Lean_Syntax_matchesNull(x_463, x_447);
if (x_465 == 0)
{
lean_object* x_466; 
lean_dec(x_463);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_466 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_462);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_467 = l_Lean_Syntax_getArg(x_463, x_17);
lean_dec(x_463);
x_468 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_469 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_468);
lean_inc(x_467);
x_470 = l_Lean_Syntax_isOfKind(x_467, x_469);
lean_dec(x_469);
if (x_470 == 0)
{
lean_object* x_471; 
lean_dec(x_467);
lean_dec(x_461);
lean_dec_ref(x_460);
lean_dec(x_459);
lean_dec_ref(x_458);
lean_dec(x_457);
lean_dec_ref(x_456);
lean_dec(x_455);
lean_dec_ref(x_454);
lean_dec(x_453);
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_449);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_471 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_462);
return x_471;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = l_Lean_Syntax_getArg(x_467, x_447);
lean_dec(x_467);
x_473 = l_Lean_Syntax_getArgs(x_472);
lean_dec(x_472);
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_473);
x_424 = x_448;
x_425 = x_449;
x_426 = x_453;
x_427 = x_452;
x_428 = x_451;
x_429 = x_474;
x_430 = x_454;
x_431 = x_455;
x_432 = x_456;
x_433 = x_457;
x_434 = x_458;
x_435 = x_459;
x_436 = x_460;
x_437 = x_461;
x_438 = x_462;
goto block_446;
}
}
}
else
{
lean_object* x_475; 
lean_dec(x_463);
x_475 = lean_box(0);
x_424 = x_448;
x_425 = x_449;
x_426 = x_453;
x_427 = x_452;
x_428 = x_451;
x_429 = x_475;
x_430 = x_454;
x_431 = x_455;
x_432 = x_456;
x_433 = x_457;
x_434 = x_458;
x_435 = x_459;
x_436 = x_460;
x_437 = x_461;
x_438 = x_462;
goto block_446;
}
}
block_505:
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; 
x_487 = lean_unsigned_to_nat(2u);
x_488 = l_Lean_Syntax_getArg(x_2, x_487);
x_489 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__4;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_490 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_489);
lean_inc(x_488);
x_491 = l_Lean_Syntax_isOfKind(x_488, x_490);
lean_dec(x_490);
if (x_491 == 0)
{
lean_object* x_492; 
lean_dec(x_488);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec_ref(x_480);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_477);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_492 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_486);
return x_492;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_493 = l_Lean_Syntax_getArg(x_488, x_17);
x_494 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_495 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_494);
lean_inc(x_493);
x_496 = l_Lean_Syntax_isOfKind(x_493, x_495);
lean_dec(x_495);
if (x_496 == 0)
{
lean_object* x_497; 
lean_dec(x_493);
lean_dec(x_488);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec_ref(x_480);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_477);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_497 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_486);
return x_497;
}
else
{
lean_object* x_498; uint8_t x_499; 
x_498 = l_Lean_Syntax_getArg(x_488, x_447);
x_499 = l_Lean_Syntax_isNone(x_498);
if (x_499 == 0)
{
uint8_t x_500; 
lean_inc(x_498);
x_500 = l_Lean_Syntax_matchesNull(x_498, x_447);
if (x_500 == 0)
{
lean_object* x_501; 
lean_dec(x_498);
lean_dec(x_493);
lean_dec(x_488);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec_ref(x_482);
lean_dec(x_481);
lean_dec_ref(x_480);
lean_dec(x_479);
lean_dec_ref(x_478);
lean_dec(x_477);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_501 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_486);
return x_501;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = l_Lean_Syntax_getArg(x_498, x_17);
lean_dec(x_498);
x_503 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_503, 0, x_502);
x_448 = x_496;
x_449 = x_493;
x_450 = x_487;
x_451 = x_477;
x_452 = x_488;
x_453 = x_503;
x_454 = x_478;
x_455 = x_479;
x_456 = x_480;
x_457 = x_481;
x_458 = x_482;
x_459 = x_483;
x_460 = x_484;
x_461 = x_485;
x_462 = x_486;
goto block_476;
}
}
else
{
lean_object* x_504; 
lean_dec(x_498);
x_504 = lean_box(0);
x_448 = x_496;
x_449 = x_493;
x_450 = x_487;
x_451 = x_477;
x_452 = x_488;
x_453 = x_504;
x_454 = x_478;
x_455 = x_479;
x_456 = x_480;
x_457 = x_481;
x_458 = x_482;
x_459 = x_483;
x_460 = x_484;
x_461 = x_485;
x_462 = x_486;
goto block_476;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalDSimpTrace___closed__0;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_12 = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_13 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_14 = l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
x_16 = 1;
x_17 = lean_box(x_15);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed), 15, 6);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_18);
lean_closure_set(x_19, 3, x_11);
lean_closure_set(x_19, 4, x_12);
lean_closure_set(x_19, 5, x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = l_Lean_Elab_Tactic_withMainContext___redArg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_1);
x_17 = lean_unbox(x_3);
x_18 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0(x_16, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_2);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDSimpTrace", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_3 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(29u);
x_2 = lean_unsigned_to_nat(82u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = lean_unsigned_to_nat(95u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(31u);
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(29u);
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(33u);
x_2 = lean_unsigned_to_nat(82u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = lean_unsigned_to_nat(82u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(47u);
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(33u);
x_4 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5;
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1;
x_3 = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_SimpTrace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ElabRules(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__0);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__8);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14);
l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15);
l_Lean_Elab_Tactic_evalSimpTrace___closed__0 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__0);
l_Lean_Elab_Tactic_evalSimpTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__3);
l_Lean_Elab_Tactic_evalSimpTrace___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__4);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__0);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3);
if (builtin) {res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__0);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__1);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__2);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__3);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__4);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__5);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3___closed__6);
if (builtin) {res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpTrace___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__0);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__1);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__2);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__3);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__4);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__5 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__5);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__6 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__6);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12);
l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__13 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__13);
l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__0);
l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__0);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1);
if (builtin) {res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__0);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__1);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__2);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__3);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__4);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__5);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3___closed__6);
if (builtin) {res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalSimpAllTrace___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0);
l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1);
l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2);
l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3);
l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__4 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__4);
l_Lean_Elab_Tactic_evalDSimpTrace___closed__0 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___closed__0);
l_Lean_Elab_Tactic_evalDSimpTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__0);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1);
if (builtin) {res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__0);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__1);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__2);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__3);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__4);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__5);
l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6 = _init_l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3___closed__6);
if (builtin) {res = l___private_Lean_Elab_Tactic_SimpTrace_0__Lean_Elab_Tactic_evalDSimpTrace___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
