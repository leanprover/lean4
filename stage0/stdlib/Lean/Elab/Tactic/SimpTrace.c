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
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_1 = lean_mk_string_unchecked("Try this:", 9, 9);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_538; uint8_t x_539; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_2, x_18);
x_477 = lean_unsigned_to_nat(1u);
x_538 = l_Lean_Syntax_getArg(x_2, x_477);
x_539 = l_Lean_Syntax_isNone(x_538);
if (x_539 == 0)
{
uint8_t x_540; 
lean_inc(x_538);
x_540 = l_Lean_Syntax_matchesNull(x_538, x_477);
if (x_540 == 0)
{
lean_object* x_541; 
lean_dec(x_538);
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
x_541 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_16);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; 
x_542 = l_Lean_Syntax_getArg(x_538, x_18);
lean_dec(x_538);
x_543 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_543, 0, x_542);
x_508 = x_543;
x_509 = x_8;
x_510 = x_9;
x_511 = x_10;
x_512 = x_11;
x_513 = x_12;
x_514 = x_13;
x_515 = x_14;
x_516 = x_15;
x_517 = x_16;
goto block_537;
}
}
else
{
lean_object* x_544; 
lean_dec(x_538);
x_544 = lean_box(0);
x_508 = x_544;
x_509 = x_8;
x_510 = x_9;
x_511 = x_10;
x_512 = x_11;
x_513 = x_12;
x_514 = x_13;
x_515 = x_14;
x_516 = x_15;
x_517 = x_16;
goto block_537;
}
block_94:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_box(x_3);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lam__1___boxed), 15, 5);
lean_closure_set(x_35, 0, x_21);
lean_closure_set(x_35, 1, x_18);
lean_closure_set(x_35, 2, x_34);
lean_closure_set(x_35, 3, x_33);
lean_closure_set(x_35, 4, x_22);
lean_inc(x_23);
lean_inc_ref(x_26);
lean_inc(x_30);
lean_inc_ref(x_24);
x_36 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(x_20, x_35, x_25, x_28, x_32, x_27, x_24, x_30, x_26, x_23, x_29);
lean_dec(x_20);
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
lean_inc(x_23);
lean_inc_ref(x_26);
lean_inc(x_30);
lean_inc_ref(x_24);
x_42 = l_Lean_Elab_Tactic_mkSimpCallStx(x_31, x_40, x_24, x_30, x_26, x_23, x_38);
lean_dec_ref(x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = lean_ctor_get(x_26, 5);
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
x_51 = 4;
x_52 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_19, x_48, x_49, x_50, x_47, x_51, x_24, x_30, x_26, x_23, x_44);
lean_dec(x_30);
lean_dec_ref(x_24);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_41);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_41);
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
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
lean_free_object(x_37);
lean_dec_ref(x_41);
lean_dec(x_30);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_19);
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
return x_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_37, 0);
x_66 = lean_ctor_get(x_37, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_37);
lean_inc(x_23);
lean_inc_ref(x_26);
lean_inc(x_30);
lean_inc_ref(x_24);
x_67 = l_Lean_Elab_Tactic_mkSimpCallStx(x_31, x_65, x_24, x_30, x_26, x_23, x_38);
lean_dec_ref(x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_ctor_get(x_26, 5);
x_71 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_74, 5, x_73);
lean_inc(x_70);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_76 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_77 = 4;
x_78 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_19, x_74, x_75, x_76, x_73, x_77, x_24, x_30, x_26, x_23, x_69);
lean_dec(x_30);
lean_dec_ref(x_24);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_66);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_66);
lean_dec(x_30);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_19);
x_86 = lean_ctor_get(x_67, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_67, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_88 = x_67;
} else {
 lean_dec_ref(x_67);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_26);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_19);
x_90 = !lean_is_exclusive(x_36);
if (x_90 == 0)
{
return x_36;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_36, 0);
x_92 = lean_ctor_get(x_36, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_36);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
block_130:
{
uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; 
x_108 = 0;
x_109 = 0;
x_110 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
lean_inc(x_106);
lean_inc_ref(x_105);
lean_inc(x_104);
lean_inc_ref(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
lean_inc(x_100);
lean_inc_ref(x_99);
x_111 = l_Lean_Elab_Tactic_mkSimpContext(x_98, x_108, x_109, x_108, x_110, x_99, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_112, 2);
lean_inc(x_116);
lean_dec(x_112);
x_20 = x_116;
x_21 = x_95;
x_22 = x_115;
x_23 = x_106;
x_24 = x_103;
x_25 = x_99;
x_26 = x_105;
x_27 = x_102;
x_28 = x_100;
x_29 = x_113;
x_30 = x_104;
x_31 = x_98;
x_32 = x_101;
x_33 = x_114;
goto block_94;
}
else
{
lean_dec_ref(x_97);
if (x_96 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
lean_dec_ref(x_111);
x_118 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_118);
x_119 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_112, 2);
lean_inc(x_120);
lean_dec(x_112);
x_20 = x_120;
x_21 = x_95;
x_22 = x_119;
x_23 = x_106;
x_24 = x_103;
x_25 = x_99;
x_26 = x_105;
x_27 = x_102;
x_28 = x_100;
x_29 = x_117;
x_30 = x_104;
x_31 = x_98;
x_32 = x_101;
x_33 = x_118;
goto block_94;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_111, 1);
lean_inc(x_121);
lean_dec_ref(x_111);
x_122 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_112, 2);
lean_inc(x_124);
lean_dec(x_112);
x_125 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_122);
x_20 = x_124;
x_21 = x_95;
x_22 = x_123;
x_23 = x_106;
x_24 = x_103;
x_25 = x_99;
x_26 = x_105;
x_27 = x_102;
x_28 = x_100;
x_29 = x_121;
x_30 = x_104;
x_31 = x_98;
x_32 = x_101;
x_33 = x_125;
goto block_94;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_19);
x_126 = !lean_is_exclusive(x_111);
if (x_126 == 0)
{
return x_111;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_111, 0);
x_128 = lean_ctor_get(x_111, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_111);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
block_156:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = l_Array_append___redArg(x_134, x_152);
lean_dec_ref(x_152);
lean_inc(x_144);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_144);
lean_ctor_set(x_154, 1, x_139);
lean_ctor_set(x_154, 2, x_153);
x_155 = l_Lean_Syntax_node6(x_144, x_137, x_133, x_145, x_150, x_135, x_142, x_154);
x_95 = x_131;
x_96 = x_141;
x_97 = x_143;
x_98 = x_155;
x_99 = x_146;
x_100 = x_148;
x_101 = x_149;
x_102 = x_140;
x_103 = x_147;
x_104 = x_132;
x_105 = x_136;
x_106 = x_138;
x_107 = x_151;
goto block_130;
}
block_185:
{
lean_object* x_179; lean_object* x_180; 
lean_inc_ref(x_160);
x_179 = l_Array_append___redArg(x_160, x_178);
lean_dec_ref(x_178);
lean_inc(x_164);
lean_inc(x_169);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_169);
lean_ctor_set(x_180, 1, x_164);
lean_ctor_set(x_180, 2, x_179);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_181; 
x_181 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_131 = x_157;
x_132 = x_158;
x_133 = x_159;
x_134 = x_160;
x_135 = x_161;
x_136 = x_162;
x_137 = x_163;
x_138 = x_165;
x_139 = x_164;
x_140 = x_166;
x_141 = x_167;
x_142 = x_180;
x_143 = x_170;
x_144 = x_169;
x_145 = x_171;
x_146 = x_168;
x_147 = x_173;
x_148 = x_172;
x_149 = x_174;
x_150 = x_175;
x_151 = x_177;
x_152 = x_181;
goto block_156;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
lean_dec_ref(x_176);
x_183 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_184 = lean_array_push(x_183, x_182);
x_131 = x_157;
x_132 = x_158;
x_133 = x_159;
x_134 = x_160;
x_135 = x_161;
x_136 = x_162;
x_137 = x_163;
x_138 = x_165;
x_139 = x_164;
x_140 = x_166;
x_141 = x_167;
x_142 = x_180;
x_143 = x_170;
x_144 = x_169;
x_145 = x_171;
x_146 = x_168;
x_147 = x_173;
x_148 = x_172;
x_149 = x_174;
x_150 = x_175;
x_151 = x_177;
x_152 = x_184;
goto block_156;
}
}
block_219:
{
lean_object* x_208; lean_object* x_209; 
lean_inc_ref(x_189);
x_208 = l_Array_append___redArg(x_189, x_207);
lean_dec_ref(x_207);
lean_inc(x_193);
lean_inc(x_197);
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_197);
lean_ctor_set(x_209, 1, x_193);
lean_ctor_set(x_209, 2, x_208);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_210; 
x_210 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_209;
x_162 = x_190;
x_163 = x_192;
x_164 = x_193;
x_165 = x_194;
x_166 = x_195;
x_167 = x_196;
x_168 = x_198;
x_169 = x_197;
x_170 = x_199;
x_171 = x_200;
x_172 = x_202;
x_173 = x_201;
x_174 = x_203;
x_175 = x_204;
x_176 = x_205;
x_177 = x_206;
x_178 = x_210;
goto block_185;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_211 = lean_ctor_get(x_191, 0);
lean_inc(x_211);
lean_dec_ref(x_191);
x_212 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_197);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_197);
lean_ctor_set(x_213, 1, x_212);
lean_inc_ref(x_189);
x_214 = l_Array_append___redArg(x_189, x_211);
lean_dec(x_211);
lean_inc(x_193);
lean_inc(x_197);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_197);
lean_ctor_set(x_215, 1, x_193);
lean_ctor_set(x_215, 2, x_214);
x_216 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_197);
x_217 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_217, 0, x_197);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Array_mkArray3___redArg(x_213, x_215, x_217);
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_209;
x_162 = x_190;
x_163 = x_192;
x_164 = x_193;
x_165 = x_194;
x_166 = x_195;
x_167 = x_196;
x_168 = x_198;
x_169 = x_197;
x_170 = x_199;
x_171 = x_200;
x_172 = x_202;
x_173 = x_201;
x_174 = x_203;
x_175 = x_204;
x_176 = x_205;
x_177 = x_206;
x_178 = x_218;
goto block_185;
}
}
block_250:
{
lean_object* x_242; lean_object* x_243; 
lean_inc_ref(x_223);
x_242 = l_Array_append___redArg(x_223, x_241);
lean_dec_ref(x_241);
lean_inc(x_228);
lean_inc(x_233);
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_233);
lean_ctor_set(x_243, 1, x_228);
lean_ctor_set(x_243, 2, x_242);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_244; 
x_244 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_186 = x_220;
x_187 = x_221;
x_188 = x_222;
x_189 = x_223;
x_190 = x_224;
x_191 = x_225;
x_192 = x_226;
x_193 = x_228;
x_194 = x_229;
x_195 = x_230;
x_196 = x_231;
x_197 = x_233;
x_198 = x_234;
x_199 = x_235;
x_200 = x_232;
x_201 = x_237;
x_202 = x_236;
x_203 = x_238;
x_204 = x_243;
x_205 = x_239;
x_206 = x_240;
x_207 = x_244;
goto block_219;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_227, 0);
lean_inc(x_245);
lean_dec_ref(x_227);
x_246 = l_Lean_SourceInfo_fromRef(x_245, x_3);
lean_dec(x_245);
x_247 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_248 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Array_mkArray1___redArg(x_248);
x_186 = x_220;
x_187 = x_221;
x_188 = x_222;
x_189 = x_223;
x_190 = x_224;
x_191 = x_225;
x_192 = x_226;
x_193 = x_228;
x_194 = x_229;
x_195 = x_230;
x_196 = x_231;
x_197 = x_233;
x_198 = x_234;
x_199 = x_235;
x_200 = x_232;
x_201 = x_237;
x_202 = x_236;
x_203 = x_238;
x_204 = x_243;
x_205 = x_239;
x_206 = x_240;
x_207 = x_249;
goto block_219;
}
}
block_276:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = l_Array_append___redArg(x_256, x_272);
lean_dec_ref(x_272);
lean_inc(x_257);
x_274 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_274, 0, x_257);
lean_ctor_set(x_274, 1, x_267);
lean_ctor_set(x_274, 2, x_273);
x_275 = l_Lean_Syntax_node6(x_257, x_270, x_259, x_263, x_254, x_268, x_255, x_274);
x_95 = x_251;
x_96 = x_261;
x_97 = x_262;
x_98 = x_275;
x_99 = x_264;
x_100 = x_266;
x_101 = x_269;
x_102 = x_260;
x_103 = x_265;
x_104 = x_252;
x_105 = x_253;
x_106 = x_258;
x_107 = x_271;
goto block_130;
}
block_304:
{
lean_object* x_299; lean_object* x_300; 
lean_inc_ref(x_281);
x_299 = l_Array_append___redArg(x_281, x_298);
lean_dec_ref(x_298);
lean_inc(x_292);
lean_inc(x_282);
x_300 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_300, 0, x_282);
lean_ctor_set(x_300, 1, x_292);
lean_ctor_set(x_300, 2, x_299);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_301; 
lean_dec_ref(x_7);
x_301 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_251 = x_277;
x_252 = x_278;
x_253 = x_279;
x_254 = x_280;
x_255 = x_300;
x_256 = x_281;
x_257 = x_282;
x_258 = x_283;
x_259 = x_284;
x_260 = x_285;
x_261 = x_286;
x_262 = x_287;
x_263 = x_288;
x_264 = x_289;
x_265 = x_291;
x_266 = x_290;
x_267 = x_292;
x_268 = x_294;
x_269 = x_293;
x_270 = x_296;
x_271 = x_297;
x_272 = x_301;
goto block_276;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_295, 0);
lean_inc(x_302);
lean_dec_ref(x_295);
x_303 = lean_apply_1(x_7, x_302);
x_251 = x_277;
x_252 = x_278;
x_253 = x_279;
x_254 = x_280;
x_255 = x_300;
x_256 = x_281;
x_257 = x_282;
x_258 = x_283;
x_259 = x_284;
x_260 = x_285;
x_261 = x_286;
x_262 = x_287;
x_263 = x_288;
x_264 = x_289;
x_265 = x_291;
x_266 = x_290;
x_267 = x_292;
x_268 = x_294;
x_269 = x_293;
x_270 = x_296;
x_271 = x_297;
x_272 = x_303;
goto block_276;
}
}
block_338:
{
lean_object* x_327; lean_object* x_328; 
lean_inc_ref(x_310);
x_327 = l_Array_append___redArg(x_310, x_326);
lean_dec_ref(x_326);
lean_inc(x_321);
lean_inc(x_311);
x_328 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_328, 0, x_311);
lean_ctor_set(x_328, 1, x_321);
lean_ctor_set(x_328, 2, x_327);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_329; 
x_329 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_277 = x_305;
x_278 = x_306;
x_279 = x_307;
x_280 = x_308;
x_281 = x_310;
x_282 = x_311;
x_283 = x_312;
x_284 = x_313;
x_285 = x_314;
x_286 = x_315;
x_287 = x_316;
x_288 = x_317;
x_289 = x_318;
x_290 = x_320;
x_291 = x_319;
x_292 = x_321;
x_293 = x_322;
x_294 = x_328;
x_295 = x_324;
x_296 = x_323;
x_297 = x_325;
x_298 = x_329;
goto block_304;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_330 = lean_ctor_get(x_309, 0);
lean_inc(x_330);
lean_dec_ref(x_309);
x_331 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_311);
x_332 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_332, 0, x_311);
lean_ctor_set(x_332, 1, x_331);
lean_inc_ref(x_310);
x_333 = l_Array_append___redArg(x_310, x_330);
lean_dec(x_330);
lean_inc(x_321);
lean_inc(x_311);
x_334 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_334, 0, x_311);
lean_ctor_set(x_334, 1, x_321);
lean_ctor_set(x_334, 2, x_333);
x_335 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_311);
x_336 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_336, 0, x_311);
lean_ctor_set(x_336, 1, x_335);
x_337 = l_Array_mkArray3___redArg(x_332, x_334, x_336);
x_277 = x_305;
x_278 = x_306;
x_279 = x_307;
x_280 = x_308;
x_281 = x_310;
x_282 = x_311;
x_283 = x_312;
x_284 = x_313;
x_285 = x_314;
x_286 = x_315;
x_287 = x_316;
x_288 = x_317;
x_289 = x_318;
x_290 = x_320;
x_291 = x_319;
x_292 = x_321;
x_293 = x_322;
x_294 = x_328;
x_295 = x_324;
x_296 = x_323;
x_297 = x_325;
x_298 = x_337;
goto block_304;
}
}
block_369:
{
lean_object* x_361; lean_object* x_362; 
lean_inc_ref(x_344);
x_361 = l_Array_append___redArg(x_344, x_360);
lean_dec_ref(x_360);
lean_inc(x_355);
lean_inc(x_345);
x_362 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_362, 0, x_345);
lean_ctor_set(x_362, 1, x_355);
lean_ctor_set(x_362, 2, x_361);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_363; 
x_363 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_305 = x_339;
x_306 = x_340;
x_307 = x_341;
x_308 = x_362;
x_309 = x_342;
x_310 = x_344;
x_311 = x_345;
x_312 = x_346;
x_313 = x_347;
x_314 = x_348;
x_315 = x_349;
x_316 = x_350;
x_317 = x_351;
x_318 = x_352;
x_319 = x_354;
x_320 = x_353;
x_321 = x_355;
x_322 = x_356;
x_323 = x_358;
x_324 = x_357;
x_325 = x_359;
x_326 = x_363;
goto block_338;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_364 = lean_ctor_get(x_343, 0);
lean_inc(x_364);
lean_dec_ref(x_343);
x_365 = l_Lean_SourceInfo_fromRef(x_364, x_3);
lean_dec(x_364);
x_366 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_367 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
x_368 = l_Array_mkArray1___redArg(x_367);
x_305 = x_339;
x_306 = x_340;
x_307 = x_341;
x_308 = x_362;
x_309 = x_342;
x_310 = x_344;
x_311 = x_345;
x_312 = x_346;
x_313 = x_347;
x_314 = x_348;
x_315 = x_349;
x_316 = x_350;
x_317 = x_351;
x_318 = x_352;
x_319 = x_354;
x_320 = x_353;
x_321 = x_355;
x_322 = x_356;
x_323 = x_358;
x_324 = x_357;
x_325 = x_359;
x_326 = x_368;
goto block_338;
}
}
block_399:
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_388 = lean_ctor_get(x_372, 5);
x_389 = l_Lean_SourceInfo_fromRef(x_388, x_387);
x_390 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__7;
x_391 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_390);
x_392 = l_Lean_SourceInfo_fromRef(x_19, x_3);
x_393 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_390);
x_394 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_395 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_396; 
x_396 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_220 = x_370;
x_221 = x_371;
x_222 = x_393;
x_223 = x_395;
x_224 = x_372;
x_225 = x_373;
x_226 = x_391;
x_227 = x_374;
x_228 = x_394;
x_229 = x_376;
x_230 = x_377;
x_231 = x_378;
x_232 = x_379;
x_233 = x_389;
x_234 = x_380;
x_235 = x_381;
x_236 = x_382;
x_237 = x_383;
x_238 = x_384;
x_239 = x_385;
x_240 = x_386;
x_241 = x_396;
goto block_250;
}
else
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_375, 0);
lean_inc(x_397);
lean_dec_ref(x_375);
x_398 = l_Array_mkArray1___redArg(x_397);
x_220 = x_370;
x_221 = x_371;
x_222 = x_393;
x_223 = x_395;
x_224 = x_372;
x_225 = x_373;
x_226 = x_391;
x_227 = x_374;
x_228 = x_394;
x_229 = x_376;
x_230 = x_377;
x_231 = x_378;
x_232 = x_379;
x_233 = x_389;
x_234 = x_380;
x_235 = x_381;
x_236 = x_382;
x_237 = x_383;
x_238 = x_384;
x_239 = x_385;
x_240 = x_386;
x_241 = x_398;
goto block_250;
}
}
block_430:
{
if (lean_obj_tag(x_410) == 0)
{
uint8_t x_416; 
lean_dec_ref(x_7);
x_416 = 0;
lean_inc(x_403);
x_370 = x_403;
x_371 = x_411;
x_372 = x_401;
x_373 = x_412;
x_374 = x_409;
x_375 = x_415;
x_376 = x_407;
x_377 = x_405;
x_378 = x_408;
x_379 = x_402;
x_380 = x_406;
x_381 = x_410;
x_382 = x_414;
x_383 = x_404;
x_384 = x_413;
x_385 = x_403;
x_386 = x_400;
x_387 = x_416;
goto block_399;
}
else
{
if (x_408 == 0)
{
lean_dec_ref(x_7);
lean_inc(x_403);
x_370 = x_403;
x_371 = x_411;
x_372 = x_401;
x_373 = x_412;
x_374 = x_409;
x_375 = x_415;
x_376 = x_407;
x_377 = x_405;
x_378 = x_408;
x_379 = x_402;
x_380 = x_406;
x_381 = x_410;
x_382 = x_414;
x_383 = x_404;
x_384 = x_413;
x_385 = x_403;
x_386 = x_400;
x_387 = x_408;
goto block_399;
}
else
{
lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_417 = lean_ctor_get(x_401, 5);
x_418 = 0;
x_419 = l_Lean_SourceInfo_fromRef(x_417, x_418);
x_420 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__11;
x_421 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_420);
x_422 = l_Lean_SourceInfo_fromRef(x_19, x_3);
x_423 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__12;
x_424 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_426 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_427; 
x_427 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
lean_inc(x_403);
x_339 = x_403;
x_340 = x_411;
x_341 = x_401;
x_342 = x_412;
x_343 = x_409;
x_344 = x_426;
x_345 = x_419;
x_346 = x_407;
x_347 = x_424;
x_348 = x_405;
x_349 = x_408;
x_350 = x_410;
x_351 = x_402;
x_352 = x_406;
x_353 = x_414;
x_354 = x_404;
x_355 = x_425;
x_356 = x_413;
x_357 = x_403;
x_358 = x_421;
x_359 = x_400;
x_360 = x_427;
goto block_369;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_415, 0);
lean_inc(x_428);
lean_dec_ref(x_415);
lean_inc_ref(x_7);
x_429 = lean_apply_1(x_7, x_428);
lean_inc(x_403);
x_339 = x_403;
x_340 = x_411;
x_341 = x_401;
x_342 = x_412;
x_343 = x_409;
x_344 = x_426;
x_345 = x_419;
x_346 = x_407;
x_347 = x_424;
x_348 = x_405;
x_349 = x_408;
x_350 = x_410;
x_351 = x_402;
x_352 = x_406;
x_353 = x_414;
x_354 = x_404;
x_355 = x_425;
x_356 = x_413;
x_357 = x_403;
x_358 = x_421;
x_359 = x_400;
x_360 = x_429;
goto block_369;
}
}
}
}
block_452:
{
lean_object* x_447; 
x_447 = l_Lean_Syntax_getOptional_x3f(x_435);
lean_dec(x_435);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; 
x_448 = lean_box(0);
x_400 = x_445;
x_401 = x_432;
x_402 = x_440;
x_403 = x_446;
x_404 = x_443;
x_405 = x_437;
x_406 = x_441;
x_407 = x_436;
x_408 = x_438;
x_409 = x_434;
x_410 = x_439;
x_411 = x_431;
x_412 = x_433;
x_413 = x_444;
x_414 = x_442;
x_415 = x_448;
goto block_430;
}
else
{
uint8_t x_449; 
x_449 = !lean_is_exclusive(x_447);
if (x_449 == 0)
{
x_400 = x_445;
x_401 = x_432;
x_402 = x_440;
x_403 = x_446;
x_404 = x_443;
x_405 = x_437;
x_406 = x_441;
x_407 = x_436;
x_408 = x_438;
x_409 = x_434;
x_410 = x_439;
x_411 = x_431;
x_412 = x_433;
x_413 = x_444;
x_414 = x_442;
x_415 = x_447;
goto block_430;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = lean_ctor_get(x_447, 0);
lean_inc(x_450);
lean_dec(x_447);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_450);
x_400 = x_445;
x_401 = x_432;
x_402 = x_440;
x_403 = x_446;
x_404 = x_443;
x_405 = x_437;
x_406 = x_441;
x_407 = x_436;
x_408 = x_438;
x_409 = x_434;
x_410 = x_439;
x_411 = x_431;
x_412 = x_433;
x_413 = x_444;
x_414 = x_442;
x_415 = x_451;
goto block_430;
}
}
}
block_476:
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_unsigned_to_nat(4u);
x_470 = l_Lean_Syntax_getArg(x_457, x_469);
lean_dec(x_457);
x_471 = l_Lean_Syntax_getOptional_x3f(x_470);
lean_dec(x_470);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; 
x_472 = lean_box(0);
x_431 = x_465;
x_432 = x_466;
x_433 = x_459;
x_434 = x_456;
x_435 = x_458;
x_436 = x_467;
x_437 = x_463;
x_438 = x_453;
x_439 = x_455;
x_440 = x_454;
x_441 = x_460;
x_442 = x_461;
x_443 = x_464;
x_444 = x_462;
x_445 = x_468;
x_446 = x_472;
goto block_452;
}
else
{
uint8_t x_473; 
x_473 = !lean_is_exclusive(x_471);
if (x_473 == 0)
{
x_431 = x_465;
x_432 = x_466;
x_433 = x_459;
x_434 = x_456;
x_435 = x_458;
x_436 = x_467;
x_437 = x_463;
x_438 = x_453;
x_439 = x_455;
x_440 = x_454;
x_441 = x_460;
x_442 = x_461;
x_443 = x_464;
x_444 = x_462;
x_445 = x_468;
x_446 = x_471;
goto block_452;
}
else
{
lean_object* x_474; lean_object* x_475; 
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
lean_dec(x_471);
x_475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_475, 0, x_474);
x_431 = x_465;
x_432 = x_466;
x_433 = x_459;
x_434 = x_456;
x_435 = x_458;
x_436 = x_467;
x_437 = x_463;
x_438 = x_453;
x_439 = x_455;
x_440 = x_454;
x_441 = x_460;
x_442 = x_461;
x_443 = x_464;
x_444 = x_462;
x_445 = x_468;
x_446 = x_475;
goto block_452;
}
}
}
block_507:
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_493 = lean_unsigned_to_nat(3u);
x_494 = l_Lean_Syntax_getArg(x_481, x_493);
x_495 = l_Lean_Syntax_isNone(x_494);
if (x_495 == 0)
{
uint8_t x_496; 
lean_inc(x_494);
x_496 = l_Lean_Syntax_matchesNull(x_494, x_477);
if (x_496 == 0)
{
lean_object* x_497; 
lean_dec(x_494);
lean_dec(x_491);
lean_dec_ref(x_490);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec_ref(x_486);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_497 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_492);
return x_497;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_498 = l_Lean_Syntax_getArg(x_494, x_18);
lean_dec(x_494);
x_499 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__13;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_500 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_499);
lean_inc(x_498);
x_501 = l_Lean_Syntax_isOfKind(x_498, x_500);
lean_dec(x_500);
if (x_501 == 0)
{
lean_object* x_502; 
lean_dec(x_498);
lean_dec(x_491);
lean_dec_ref(x_490);
lean_dec(x_489);
lean_dec_ref(x_488);
lean_dec(x_487);
lean_dec_ref(x_486);
lean_dec(x_485);
lean_dec_ref(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_502 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_492);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = l_Lean_Syntax_getArg(x_498, x_477);
lean_dec(x_498);
x_504 = l_Lean_Syntax_getArgs(x_503);
lean_dec(x_503);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_504);
x_453 = x_478;
x_454 = x_480;
x_455 = x_479;
x_456 = x_483;
x_457 = x_481;
x_458 = x_482;
x_459 = x_505;
x_460 = x_484;
x_461 = x_485;
x_462 = x_486;
x_463 = x_487;
x_464 = x_488;
x_465 = x_489;
x_466 = x_490;
x_467 = x_491;
x_468 = x_492;
goto block_476;
}
}
}
else
{
lean_object* x_506; 
lean_dec(x_494);
x_506 = lean_box(0);
x_453 = x_478;
x_454 = x_480;
x_455 = x_479;
x_456 = x_483;
x_457 = x_481;
x_458 = x_482;
x_459 = x_506;
x_460 = x_484;
x_461 = x_485;
x_462 = x_486;
x_463 = x_487;
x_464 = x_488;
x_465 = x_489;
x_466 = x_490;
x_467 = x_491;
x_468 = x_492;
goto block_476;
}
}
block_537:
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_518 = lean_unsigned_to_nat(2u);
x_519 = l_Lean_Syntax_getArg(x_2, x_518);
x_520 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__14;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_521 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_520);
lean_inc(x_519);
x_522 = l_Lean_Syntax_isOfKind(x_519, x_521);
lean_dec(x_521);
if (x_522 == 0)
{
lean_object* x_523; 
lean_dec(x_519);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_512);
lean_dec_ref(x_511);
lean_dec(x_510);
lean_dec_ref(x_509);
lean_dec(x_508);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_523 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_517);
return x_523;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_524 = l_Lean_Syntax_getArg(x_519, x_18);
x_525 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_526 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_525);
lean_inc(x_524);
x_527 = l_Lean_Syntax_isOfKind(x_524, x_526);
lean_dec(x_526);
if (x_527 == 0)
{
lean_object* x_528; 
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_512);
lean_dec_ref(x_511);
lean_dec(x_510);
lean_dec_ref(x_509);
lean_dec(x_508);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_528 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_517);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; 
x_529 = l_Lean_Syntax_getArg(x_519, x_477);
x_530 = l_Lean_Syntax_getArg(x_519, x_518);
x_531 = l_Lean_Syntax_isNone(x_530);
if (x_531 == 0)
{
uint8_t x_532; 
lean_inc(x_530);
x_532 = l_Lean_Syntax_matchesNull(x_530, x_477);
if (x_532 == 0)
{
lean_object* x_533; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_524);
lean_dec(x_519);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_512);
lean_dec_ref(x_511);
lean_dec(x_510);
lean_dec_ref(x_509);
lean_dec(x_508);
lean_dec(x_19);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_533 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_517);
return x_533;
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = l_Lean_Syntax_getArg(x_530, x_18);
lean_dec(x_530);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_534);
x_478 = x_527;
x_479 = x_508;
x_480 = x_524;
x_481 = x_519;
x_482 = x_529;
x_483 = x_535;
x_484 = x_509;
x_485 = x_510;
x_486 = x_511;
x_487 = x_512;
x_488 = x_513;
x_489 = x_514;
x_490 = x_515;
x_491 = x_516;
x_492 = x_517;
goto block_507;
}
}
else
{
lean_object* x_536; 
lean_dec(x_530);
x_536 = lean_box(0);
x_478 = x_527;
x_479 = x_508;
x_480 = x_524;
x_481 = x_519;
x_482 = x_529;
x_483 = x_536;
x_484 = x_509;
x_485 = x_510;
x_486 = x_511;
x_487 = x_512;
x_488 = x_513;
x_489 = x_514;
x_490 = x_515;
x_491 = x_516;
x_492 = x_517;
goto block_507;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_478; uint8_t x_479; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_417 = lean_unsigned_to_nat(1u);
x_478 = l_Lean_Syntax_getArg(x_2, x_417);
x_479 = l_Lean_Syntax_isNone(x_478);
if (x_479 == 0)
{
uint8_t x_480; 
lean_inc(x_478);
x_480 = l_Lean_Syntax_matchesNull(x_478, x_417);
if (x_480 == 0)
{
lean_object* x_481; 
lean_dec(x_478);
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
x_481 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_15);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; 
x_482 = l_Lean_Syntax_getArg(x_478, x_17);
lean_dec(x_478);
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_448 = x_483;
x_449 = x_7;
x_450 = x_8;
x_451 = x_9;
x_452 = x_10;
x_453 = x_11;
x_454 = x_12;
x_455 = x_13;
x_456 = x_14;
x_457 = x_15;
goto block_477;
}
}
else
{
lean_object* x_484; 
lean_dec(x_478);
x_484 = lean_box(0);
x_448 = x_484;
x_449 = x_7;
x_450 = x_8;
x_451 = x_9;
x_452 = x_10;
x_453 = x_11;
x_454 = x_12;
x_455 = x_13;
x_456 = x_14;
x_457 = x_15;
goto block_477;
}
block_77:
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
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
x_38 = 4;
x_39 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_35, x_36, x_37, x_34, x_38, x_21, x_22, x_23, x_24, x_31);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_28);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec_ref(x_28);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_20);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
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
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_54 = l_Lean_Elab_Tactic_mkSimpCallStx(x_19, x_52, x_21, x_22, x_23, x_24, x_25);
lean_dec_ref(x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_ctor_get(x_23, 5);
x_58 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_60);
lean_inc(x_57);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_63 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_64 = 4;
x_65 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_61, x_62, x_63, x_60, x_64, x_21, x_22, x_23, x_24, x_56);
lean_dec(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_53);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_53);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_53);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_18);
x_73 = lean_ctor_get(x_54, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_75 = x_54;
} else {
 lean_dec_ref(x_54);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
block_133:
{
lean_object* x_87; 
x_87 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_80, x_85, x_84, x_78, x_82, x_81);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
x_90 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__7;
lean_inc(x_82);
lean_inc_ref(x_78);
lean_inc(x_84);
lean_inc_ref(x_85);
x_91 = l_Lean_Meta_simpAll(x_88, x_86, x_83, x_90, x_85, x_84, x_78, x_82, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec_ref(x_91);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_box(0);
x_97 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_96, x_80, x_85, x_84, x_78, x_82, x_94);
lean_dec(x_80);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec_ref(x_97);
x_19 = x_79;
x_20 = x_95;
x_21 = x_85;
x_22 = x_84;
x_23 = x_78;
x_24 = x_82;
x_25 = x_98;
goto block_77;
}
else
{
uint8_t x_99; 
lean_dec(x_95);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_18);
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_97);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; uint8_t x_104; 
lean_inc_ref(x_93);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
lean_dec_ref(x_91);
x_104 = !lean_is_exclusive(x_92);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_92, 1);
x_106 = lean_ctor_get(x_92, 0);
lean_dec(x_106);
x_107 = lean_ctor_get(x_93, 0);
lean_inc(x_107);
lean_dec_ref(x_93);
x_108 = lean_box(0);
lean_ctor_set_tag(x_92, 1);
lean_ctor_set(x_92, 1, x_108);
lean_ctor_set(x_92, 0, x_107);
x_109 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_92, x_80, x_85, x_84, x_78, x_82, x_103);
lean_dec(x_80);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
x_19 = x_79;
x_20 = x_105;
x_21 = x_85;
x_22 = x_84;
x_23 = x_78;
x_24 = x_82;
x_25 = x_110;
goto block_77;
}
else
{
uint8_t x_111; 
lean_dec(x_105);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_18);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
return x_109;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_109, 0);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_109);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_92, 1);
lean_inc(x_115);
lean_dec(x_92);
x_116 = lean_ctor_get(x_93, 0);
lean_inc(x_116);
lean_dec_ref(x_93);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_118, x_80, x_85, x_84, x_78, x_82, x_103);
lean_dec(x_80);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec_ref(x_119);
x_19 = x_79;
x_20 = x_115;
x_21 = x_85;
x_22 = x_84;
x_23 = x_78;
x_24 = x_82;
x_25 = x_120;
goto block_77;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_115);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_18);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_123 = x_119;
} else {
 lean_dec_ref(x_119);
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
}
}
else
{
uint8_t x_125; 
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_18);
x_125 = !lean_is_exclusive(x_91);
if (x_125 == 0)
{
return x_91;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_91, 0);
x_127 = lean_ctor_get(x_91, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_91);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec_ref(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_18);
x_129 = !lean_is_exclusive(x_87);
if (x_129 == 0)
{
return x_87;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_87, 0);
x_131 = lean_ctor_get(x_87, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_87);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
block_164:
{
uint8_t x_146; lean_object* x_147; lean_object* x_148; 
x_146 = 1;
x_147 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
lean_inc(x_144);
lean_inc_ref(x_143);
lean_inc(x_142);
lean_inc_ref(x_141);
lean_inc(x_138);
x_148 = l_Lean_Elab_Tactic_mkSimpContext(x_136, x_3, x_146, x_3, x_147, x_137, x_138, x_139, x_140, x_141, x_142, x_143, x_144, x_145);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec_ref(x_148);
x_151 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_152);
lean_dec(x_149);
x_78 = x_143;
x_79 = x_136;
x_80 = x_138;
x_81 = x_150;
x_82 = x_144;
x_83 = x_152;
x_84 = x_142;
x_85 = x_141;
x_86 = x_151;
goto block_133;
}
else
{
lean_dec_ref(x_134);
if (x_135 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_148, 1);
lean_inc(x_153);
lean_dec_ref(x_148);
x_154 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_154);
x_155 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_155);
lean_dec(x_149);
x_78 = x_143;
x_79 = x_136;
x_80 = x_138;
x_81 = x_153;
x_82 = x_144;
x_83 = x_155;
x_84 = x_142;
x_85 = x_141;
x_86 = x_154;
goto block_133;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
lean_dec_ref(x_148);
x_157 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_158);
lean_dec(x_149);
x_159 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_157);
x_78 = x_143;
x_79 = x_136;
x_80 = x_138;
x_81 = x_156;
x_82 = x_144;
x_83 = x_158;
x_84 = x_142;
x_85 = x_141;
x_86 = x_159;
goto block_133;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_18);
x_160 = !lean_is_exclusive(x_148);
if (x_160 == 0)
{
return x_148;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_148, 0);
x_162 = lean_ctor_get(x_148, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_148);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
block_188:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = l_Array_append___redArg(x_165, x_184);
lean_dec_ref(x_184);
lean_inc(x_170);
x_186 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_186, 0, x_170);
lean_ctor_set(x_186, 1, x_173);
lean_ctor_set(x_186, 2, x_185);
x_187 = l_Lean_Syntax_node5(x_170, x_178, x_176, x_166, x_183, x_167, x_186);
x_134 = x_180;
x_135 = x_171;
x_136 = x_187;
x_137 = x_179;
x_138 = x_168;
x_139 = x_169;
x_140 = x_174;
x_141 = x_175;
x_142 = x_181;
x_143 = x_182;
x_144 = x_177;
x_145 = x_172;
goto block_164;
}
block_220:
{
lean_object* x_209; lean_object* x_210; 
lean_inc_ref(x_189);
x_209 = l_Array_append___redArg(x_189, x_208);
lean_dec_ref(x_208);
lean_inc(x_196);
lean_inc(x_193);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_193);
lean_ctor_set(x_210, 1, x_196);
lean_ctor_set(x_210, 2, x_209);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_211; 
x_211 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_165 = x_189;
x_166 = x_190;
x_167 = x_210;
x_168 = x_191;
x_169 = x_192;
x_170 = x_193;
x_171 = x_194;
x_172 = x_195;
x_173 = x_196;
x_174 = x_197;
x_175 = x_198;
x_176 = x_199;
x_177 = x_200;
x_178 = x_201;
x_179 = x_202;
x_180 = x_204;
x_181 = x_205;
x_182 = x_206;
x_183 = x_207;
x_184 = x_211;
goto block_188;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_212 = lean_ctor_get(x_203, 0);
lean_inc(x_212);
lean_dec_ref(x_203);
x_213 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_193);
x_214 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_214, 0, x_193);
lean_ctor_set(x_214, 1, x_213);
lean_inc_ref(x_189);
x_215 = l_Array_append___redArg(x_189, x_212);
lean_dec(x_212);
lean_inc(x_196);
lean_inc(x_193);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_193);
lean_ctor_set(x_216, 1, x_196);
lean_ctor_set(x_216, 2, x_215);
x_217 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_193);
x_218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_218, 0, x_193);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Array_mkArray3___redArg(x_214, x_216, x_218);
x_165 = x_189;
x_166 = x_190;
x_167 = x_210;
x_168 = x_191;
x_169 = x_192;
x_170 = x_193;
x_171 = x_194;
x_172 = x_195;
x_173 = x_196;
x_174 = x_197;
x_175 = x_198;
x_176 = x_199;
x_177 = x_200;
x_178 = x_201;
x_179 = x_202;
x_180 = x_204;
x_181 = x_205;
x_182 = x_206;
x_183 = x_207;
x_184 = x_219;
goto block_188;
}
}
block_249:
{
lean_object* x_241; lean_object* x_242; 
lean_inc_ref(x_221);
x_241 = l_Array_append___redArg(x_221, x_240);
lean_dec_ref(x_240);
lean_inc(x_228);
lean_inc(x_225);
x_242 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_242, 0, x_225);
lean_ctor_set(x_242, 1, x_228);
lean_ctor_set(x_242, 2, x_241);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_243; 
x_243 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_189 = x_221;
x_190 = x_222;
x_191 = x_223;
x_192 = x_224;
x_193 = x_225;
x_194 = x_226;
x_195 = x_227;
x_196 = x_228;
x_197 = x_229;
x_198 = x_230;
x_199 = x_231;
x_200 = x_232;
x_201 = x_233;
x_202 = x_235;
x_203 = x_237;
x_204 = x_236;
x_205 = x_238;
x_206 = x_239;
x_207 = x_242;
x_208 = x_243;
goto block_220;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_244 = lean_ctor_get(x_234, 0);
lean_inc(x_244);
lean_dec_ref(x_234);
x_245 = l_Lean_SourceInfo_fromRef(x_244, x_3);
lean_dec(x_244);
x_246 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_247 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Array_mkArray1___redArg(x_247);
x_189 = x_221;
x_190 = x_222;
x_191 = x_223;
x_192 = x_224;
x_193 = x_225;
x_194 = x_226;
x_195 = x_227;
x_196 = x_228;
x_197 = x_229;
x_198 = x_230;
x_199 = x_231;
x_200 = x_232;
x_201 = x_233;
x_202 = x_235;
x_203 = x_237;
x_204 = x_236;
x_205 = x_238;
x_206 = x_239;
x_207 = x_242;
x_208 = x_248;
goto block_220;
}
}
block_273:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = l_Array_append___redArg(x_262, x_269);
lean_dec_ref(x_269);
lean_inc(x_251);
x_271 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_271, 0, x_251);
lean_ctor_set(x_271, 1, x_260);
lean_ctor_set(x_271, 2, x_270);
x_272 = l_Lean_Syntax_node5(x_251, x_254, x_266, x_250, x_267, x_255, x_271);
x_134 = x_264;
x_135 = x_256;
x_136 = x_272;
x_137 = x_263;
x_138 = x_252;
x_139 = x_253;
x_140 = x_258;
x_141 = x_259;
x_142 = x_265;
x_143 = x_268;
x_144 = x_261;
x_145 = x_257;
goto block_164;
}
block_305:
{
lean_object* x_294; lean_object* x_295; 
lean_inc_ref(x_285);
x_294 = l_Array_append___redArg(x_285, x_293);
lean_dec_ref(x_293);
lean_inc(x_283);
lean_inc(x_275);
x_295 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_295, 0, x_275);
lean_ctor_set(x_295, 1, x_283);
lean_ctor_set(x_295, 2, x_294);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_296; 
x_296 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_250 = x_274;
x_251 = x_275;
x_252 = x_276;
x_253 = x_277;
x_254 = x_278;
x_255 = x_295;
x_256 = x_279;
x_257 = x_280;
x_258 = x_281;
x_259 = x_282;
x_260 = x_283;
x_261 = x_284;
x_262 = x_285;
x_263 = x_286;
x_264 = x_288;
x_265 = x_291;
x_266 = x_290;
x_267 = x_289;
x_268 = x_292;
x_269 = x_296;
goto block_273;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_297 = lean_ctor_get(x_287, 0);
lean_inc(x_297);
lean_dec_ref(x_287);
x_298 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_275);
x_299 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_299, 0, x_275);
lean_ctor_set(x_299, 1, x_298);
lean_inc_ref(x_285);
x_300 = l_Array_append___redArg(x_285, x_297);
lean_dec(x_297);
lean_inc(x_283);
lean_inc(x_275);
x_301 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_301, 0, x_275);
lean_ctor_set(x_301, 1, x_283);
lean_ctor_set(x_301, 2, x_300);
x_302 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_275);
x_303 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_303, 0, x_275);
lean_ctor_set(x_303, 1, x_302);
x_304 = l_Array_mkArray3___redArg(x_299, x_301, x_303);
x_250 = x_274;
x_251 = x_275;
x_252 = x_276;
x_253 = x_277;
x_254 = x_278;
x_255 = x_295;
x_256 = x_279;
x_257 = x_280;
x_258 = x_281;
x_259 = x_282;
x_260 = x_283;
x_261 = x_284;
x_262 = x_285;
x_263 = x_286;
x_264 = x_288;
x_265 = x_291;
x_266 = x_290;
x_267 = x_289;
x_268 = x_292;
x_269 = x_304;
goto block_273;
}
}
block_334:
{
lean_object* x_326; lean_object* x_327; 
lean_inc_ref(x_317);
x_326 = l_Array_append___redArg(x_317, x_325);
lean_dec_ref(x_325);
lean_inc(x_315);
lean_inc(x_307);
x_327 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_327, 0, x_307);
lean_ctor_set(x_327, 1, x_315);
lean_ctor_set(x_327, 2, x_326);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_328; 
x_328 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_274 = x_306;
x_275 = x_307;
x_276 = x_308;
x_277 = x_309;
x_278 = x_310;
x_279 = x_311;
x_280 = x_312;
x_281 = x_313;
x_282 = x_314;
x_283 = x_315;
x_284 = x_316;
x_285 = x_317;
x_286 = x_319;
x_287 = x_321;
x_288 = x_320;
x_289 = x_327;
x_290 = x_323;
x_291 = x_322;
x_292 = x_324;
x_293 = x_328;
goto block_305;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_329 = lean_ctor_get(x_318, 0);
lean_inc(x_329);
lean_dec_ref(x_318);
x_330 = l_Lean_SourceInfo_fromRef(x_329, x_3);
lean_dec(x_329);
x_331 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_332 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = l_Array_mkArray1___redArg(x_332);
x_274 = x_306;
x_275 = x_307;
x_276 = x_308;
x_277 = x_309;
x_278 = x_310;
x_279 = x_311;
x_280 = x_312;
x_281 = x_313;
x_282 = x_314;
x_283 = x_315;
x_284 = x_316;
x_285 = x_317;
x_286 = x_319;
x_287 = x_321;
x_288 = x_320;
x_289 = x_327;
x_290 = x_323;
x_291 = x_322;
x_292 = x_324;
x_293 = x_333;
goto block_305;
}
}
block_364:
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_351 = lean_ctor_get(x_349, 5);
x_352 = l_Lean_SourceInfo_fromRef(x_351, x_350);
x_353 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__8;
x_354 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_353);
x_355 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_356 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__9;
x_357 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_359 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_360; 
x_360 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_221 = x_359;
x_222 = x_335;
x_223 = x_336;
x_224 = x_337;
x_225 = x_352;
x_226 = x_338;
x_227 = x_339;
x_228 = x_358;
x_229 = x_340;
x_230 = x_341;
x_231 = x_357;
x_232 = x_342;
x_233 = x_354;
x_234 = x_343;
x_235 = x_344;
x_236 = x_345;
x_237 = x_346;
x_238 = x_347;
x_239 = x_349;
x_240 = x_360;
goto block_249;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_348, 0);
lean_inc(x_361);
lean_dec_ref(x_348);
x_362 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_363 = lean_array_push(x_362, x_361);
x_221 = x_359;
x_222 = x_335;
x_223 = x_336;
x_224 = x_337;
x_225 = x_352;
x_226 = x_338;
x_227 = x_339;
x_228 = x_358;
x_229 = x_340;
x_230 = x_341;
x_231 = x_357;
x_232 = x_342;
x_233 = x_354;
x_234 = x_343;
x_235 = x_344;
x_236 = x_345;
x_237 = x_346;
x_238 = x_347;
x_239 = x_349;
x_240 = x_363;
goto block_249;
}
}
block_395:
{
if (lean_obj_tag(x_375) == 0)
{
uint8_t x_380; 
x_380 = 0;
x_335 = x_365;
x_336 = x_366;
x_337 = x_367;
x_338 = x_368;
x_339 = x_369;
x_340 = x_370;
x_341 = x_371;
x_342 = x_372;
x_343 = x_373;
x_344 = x_374;
x_345 = x_375;
x_346 = x_376;
x_347 = x_377;
x_348 = x_379;
x_349 = x_378;
x_350 = x_380;
goto block_364;
}
else
{
if (x_368 == 0)
{
x_335 = x_365;
x_336 = x_366;
x_337 = x_367;
x_338 = x_368;
x_339 = x_369;
x_340 = x_370;
x_341 = x_371;
x_342 = x_372;
x_343 = x_373;
x_344 = x_374;
x_345 = x_375;
x_346 = x_376;
x_347 = x_377;
x_348 = x_379;
x_349 = x_378;
x_350 = x_368;
goto block_364;
}
else
{
lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_381 = lean_ctor_get(x_378, 5);
x_382 = 0;
x_383 = l_Lean_SourceInfo_fromRef(x_381, x_382);
x_384 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__10;
x_385 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_384);
x_386 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_387 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__11;
x_388 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_389 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_390 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_391; 
x_391 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_306 = x_365;
x_307 = x_383;
x_308 = x_366;
x_309 = x_367;
x_310 = x_385;
x_311 = x_368;
x_312 = x_369;
x_313 = x_370;
x_314 = x_371;
x_315 = x_389;
x_316 = x_372;
x_317 = x_390;
x_318 = x_373;
x_319 = x_374;
x_320 = x_375;
x_321 = x_376;
x_322 = x_377;
x_323 = x_388;
x_324 = x_378;
x_325 = x_391;
goto block_334;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_379, 0);
lean_inc(x_392);
lean_dec_ref(x_379);
x_393 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_394 = lean_array_push(x_393, x_392);
x_306 = x_365;
x_307 = x_383;
x_308 = x_366;
x_309 = x_367;
x_310 = x_385;
x_311 = x_368;
x_312 = x_369;
x_313 = x_370;
x_314 = x_371;
x_315 = x_389;
x_316 = x_372;
x_317 = x_390;
x_318 = x_373;
x_319 = x_374;
x_320 = x_375;
x_321 = x_376;
x_322 = x_377;
x_323 = x_388;
x_324 = x_378;
x_325 = x_394;
goto block_334;
}
}
}
}
block_416:
{
lean_object* x_411; 
x_411 = l_Lean_Syntax_getOptional_x3f(x_397);
lean_dec(x_397);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; 
x_412 = lean_box(0);
x_365 = x_396;
x_366 = x_403;
x_367 = x_404;
x_368 = x_400;
x_369 = x_410;
x_370 = x_405;
x_371 = x_406;
x_372 = x_409;
x_373 = x_398;
x_374 = x_402;
x_375 = x_399;
x_376 = x_401;
x_377 = x_407;
x_378 = x_408;
x_379 = x_412;
goto block_395;
}
else
{
uint8_t x_413; 
x_413 = !lean_is_exclusive(x_411);
if (x_413 == 0)
{
x_365 = x_396;
x_366 = x_403;
x_367 = x_404;
x_368 = x_400;
x_369 = x_410;
x_370 = x_405;
x_371 = x_406;
x_372 = x_409;
x_373 = x_398;
x_374 = x_402;
x_375 = x_399;
x_376 = x_401;
x_377 = x_407;
x_378 = x_408;
x_379 = x_411;
goto block_395;
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_411, 0);
lean_inc(x_414);
lean_dec(x_411);
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_414);
x_365 = x_396;
x_366 = x_403;
x_367 = x_404;
x_368 = x_400;
x_369 = x_410;
x_370 = x_405;
x_371 = x_406;
x_372 = x_409;
x_373 = x_398;
x_374 = x_402;
x_375 = x_399;
x_376 = x_401;
x_377 = x_407;
x_378 = x_408;
x_379 = x_415;
goto block_395;
}
}
}
block_447:
{
lean_object* x_433; lean_object* x_434; uint8_t x_435; 
x_433 = lean_unsigned_to_nat(3u);
x_434 = l_Lean_Syntax_getArg(x_420, x_433);
lean_dec(x_420);
x_435 = l_Lean_Syntax_isNone(x_434);
if (x_435 == 0)
{
uint8_t x_436; 
lean_inc(x_434);
x_436 = l_Lean_Syntax_matchesNull(x_434, x_417);
if (x_436 == 0)
{
lean_object* x_437; 
lean_dec(x_434);
lean_dec(x_431);
lean_dec_ref(x_430);
lean_dec(x_429);
lean_dec_ref(x_428);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_437 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_432);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_438 = l_Lean_Syntax_getArg(x_434, x_17);
lean_dec(x_434);
x_439 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_440 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_439);
lean_inc(x_438);
x_441 = l_Lean_Syntax_isOfKind(x_438, x_440);
lean_dec(x_440);
if (x_441 == 0)
{
lean_object* x_442; 
lean_dec(x_438);
lean_dec(x_431);
lean_dec_ref(x_430);
lean_dec(x_429);
lean_dec_ref(x_428);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_442 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_432);
return x_442;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = l_Lean_Syntax_getArg(x_438, x_417);
lean_dec(x_438);
x_444 = l_Lean_Syntax_getArgs(x_443);
lean_dec(x_443);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
x_396 = x_418;
x_397 = x_419;
x_398 = x_423;
x_399 = x_421;
x_400 = x_422;
x_401 = x_445;
x_402 = x_424;
x_403 = x_425;
x_404 = x_426;
x_405 = x_427;
x_406 = x_428;
x_407 = x_429;
x_408 = x_430;
x_409 = x_431;
x_410 = x_432;
goto block_416;
}
}
}
else
{
lean_object* x_446; 
lean_dec(x_434);
x_446 = lean_box(0);
x_396 = x_418;
x_397 = x_419;
x_398 = x_423;
x_399 = x_421;
x_400 = x_422;
x_401 = x_446;
x_402 = x_424;
x_403 = x_425;
x_404 = x_426;
x_405 = x_427;
x_406 = x_428;
x_407 = x_429;
x_408 = x_430;
x_409 = x_431;
x_410 = x_432;
goto block_416;
}
}
block_477:
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_458 = lean_unsigned_to_nat(2u);
x_459 = l_Lean_Syntax_getArg(x_2, x_458);
x_460 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__13;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_461 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_460);
lean_inc(x_459);
x_462 = l_Lean_Syntax_isOfKind(x_459, x_461);
lean_dec(x_461);
if (x_462 == 0)
{
lean_object* x_463; 
lean_dec(x_459);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_451);
lean_dec(x_450);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_463 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_457);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; 
x_464 = l_Lean_Syntax_getArg(x_459, x_17);
x_465 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_466 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_465);
lean_inc(x_464);
x_467 = l_Lean_Syntax_isOfKind(x_464, x_466);
lean_dec(x_466);
if (x_467 == 0)
{
lean_object* x_468; 
lean_dec(x_464);
lean_dec(x_459);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_451);
lean_dec(x_450);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_468 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_457);
return x_468;
}
else
{
lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_469 = l_Lean_Syntax_getArg(x_459, x_417);
x_470 = l_Lean_Syntax_getArg(x_459, x_458);
x_471 = l_Lean_Syntax_isNone(x_470);
if (x_471 == 0)
{
uint8_t x_472; 
lean_inc(x_470);
x_472 = l_Lean_Syntax_matchesNull(x_470, x_417);
if (x_472 == 0)
{
lean_object* x_473; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_464);
lean_dec(x_459);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec(x_454);
lean_dec_ref(x_453);
lean_dec(x_452);
lean_dec_ref(x_451);
lean_dec(x_450);
lean_dec_ref(x_449);
lean_dec(x_448);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_473 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_457);
return x_473;
}
else
{
lean_object* x_474; lean_object* x_475; 
x_474 = l_Lean_Syntax_getArg(x_470, x_17);
lean_dec(x_470);
x_475 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_475, 0, x_474);
x_418 = x_464;
x_419 = x_469;
x_420 = x_459;
x_421 = x_448;
x_422 = x_467;
x_423 = x_475;
x_424 = x_449;
x_425 = x_450;
x_426 = x_451;
x_427 = x_452;
x_428 = x_453;
x_429 = x_454;
x_430 = x_455;
x_431 = x_456;
x_432 = x_457;
goto block_447;
}
}
else
{
lean_object* x_476; 
lean_dec(x_470);
x_476 = lean_box(0);
x_418 = x_464;
x_419 = x_469;
x_420 = x_459;
x_421 = x_448;
x_422 = x_467;
x_423 = x_476;
x_424 = x_449;
x_425 = x_450;
x_426 = x_451;
x_427 = x_452;
x_428 = x_453;
x_429 = x_454;
x_430 = x_455;
x_431 = x_456;
x_432 = x_457;
goto block_447;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_468; uint8_t x_469; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_409 = lean_unsigned_to_nat(1u);
x_468 = l_Lean_Syntax_getArg(x_2, x_409);
x_469 = l_Lean_Syntax_isNone(x_468);
if (x_469 == 0)
{
uint8_t x_470; 
lean_inc(x_468);
x_470 = l_Lean_Syntax_matchesNull(x_468, x_409);
if (x_470 == 0)
{
lean_object* x_471; 
lean_dec(x_468);
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
x_471 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_15);
return x_471;
}
else
{
lean_object* x_472; lean_object* x_473; 
x_472 = l_Lean_Syntax_getArg(x_468, x_17);
lean_dec(x_468);
x_473 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_473, 0, x_472);
x_439 = x_473;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_12;
x_446 = x_13;
x_447 = x_14;
x_448 = x_15;
goto block_467;
}
}
else
{
lean_object* x_474; 
lean_dec(x_468);
x_474 = lean_box(0);
x_439 = x_474;
x_440 = x_7;
x_441 = x_8;
x_442 = x_9;
x_443 = x_10;
x_444 = x_11;
x_445 = x_12;
x_446 = x_13;
x_447 = x_14;
x_448 = x_15;
goto block_467;
}
block_90:
{
lean_object* x_32; 
lean_inc(x_25);
lean_inc_ref(x_22);
lean_inc(x_23);
lean_inc_ref(x_27);
x_32 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_21, x_19, x_31, x_30, x_29, x_28, x_26, x_27, x_23, x_22, x_25, x_20);
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
lean_inc(x_25);
lean_inc_ref(x_22);
lean_inc(x_23);
lean_inc_ref(x_27);
x_38 = l_Lean_Elab_Tactic_mkSimpCallStx(x_24, x_36, x_27, x_23, x_22, x_25, x_34);
lean_dec_ref(x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
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
x_47 = 4;
x_48 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_44, x_45, x_46, x_43, x_47, x_27, x_23, x_22, x_25, x_40);
lean_dec(x_23);
lean_dec_ref(x_27);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_37);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_37);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
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
lean_free_object(x_33);
lean_dec_ref(x_37);
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_18);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
return x_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_33, 0);
x_62 = lean_ctor_get(x_33, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_33);
lean_inc(x_25);
lean_inc_ref(x_22);
lean_inc(x_23);
lean_inc_ref(x_27);
x_63 = l_Lean_Elab_Tactic_mkSimpCallStx(x_24, x_61, x_27, x_23, x_22, x_25, x_34);
lean_dec_ref(x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_ctor_get(x_22, 5);
x_67 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__1;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_69);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_69);
lean_inc(x_66);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_72 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__2;
x_73 = 4;
x_74 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_18, x_70, x_71, x_72, x_69, x_73, x_27, x_23, x_22, x_25, x_65);
lean_dec(x_23);
lean_dec_ref(x_27);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_62);
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_62);
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_18);
x_82 = lean_ctor_get(x_63, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_63, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_84 = x_63;
} else {
 lean_dec_ref(x_63);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_18);
x_86 = !lean_is_exclusive(x_32);
if (x_86 == 0)
{
return x_32;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_32, 0);
x_88 = lean_ctor_get(x_32, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_32);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
block_108:
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__0;
x_105 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_3);
x_19 = x_91;
x_20 = x_92;
x_21 = x_103;
x_22 = x_93;
x_23 = x_94;
x_24 = x_97;
x_25 = x_96;
x_26 = x_95;
x_27 = x_98;
x_28 = x_99;
x_29 = x_101;
x_30 = x_102;
x_31 = x_105;
goto block_90;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec_ref(x_100);
x_107 = l_Lean_Elab_Tactic_expandLocation(x_106);
lean_dec(x_106);
x_19 = x_91;
x_20 = x_92;
x_21 = x_103;
x_22 = x_93;
x_23 = x_94;
x_24 = x_97;
x_25 = x_96;
x_26 = x_95;
x_27 = x_98;
x_28 = x_99;
x_29 = x_101;
x_30 = x_102;
x_31 = x_107;
goto block_90;
}
}
block_145:
{
uint8_t x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = 0;
x_123 = 2;
x_124 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__3;
x_125 = lean_box(x_122);
x_126 = lean_box(x_123);
x_127 = lean_box(x_122);
lean_inc(x_112);
x_128 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_128, 0, x_112);
lean_closure_set(x_128, 1, x_125);
lean_closure_set(x_128, 2, x_126);
lean_closure_set(x_128, 3, x_127);
lean_closure_set(x_128, 4, x_124);
lean_inc(x_120);
lean_inc_ref(x_119);
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc(x_114);
lean_inc_ref(x_113);
x_129 = l_Lean_Elab_Tactic_withMainContext___redArg(x_128, x_113, x_114, x_115, x_116, x_117, x_118, x_119, x_120, x_121);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc_ref(x_133);
lean_dec(x_130);
x_91 = x_133;
x_92 = x_131;
x_93 = x_119;
x_94 = x_118;
x_95 = x_116;
x_96 = x_120;
x_97 = x_112;
x_98 = x_117;
x_99 = x_115;
x_100 = x_111;
x_101 = x_114;
x_102 = x_113;
x_103 = x_132;
goto block_108;
}
else
{
lean_dec_ref(x_109);
if (x_110 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_dec_ref(x_129);
x_135 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc_ref(x_136);
lean_dec(x_130);
x_91 = x_136;
x_92 = x_134;
x_93 = x_119;
x_94 = x_118;
x_95 = x_116;
x_96 = x_120;
x_97 = x_112;
x_98 = x_117;
x_99 = x_115;
x_100 = x_111;
x_101 = x_114;
x_102 = x_113;
x_103 = x_135;
goto block_108;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_129, 1);
lean_inc(x_137);
lean_dec_ref(x_129);
x_138 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_130, 1);
lean_inc_ref(x_139);
lean_dec(x_130);
x_140 = l_Lean_Meta_Simp_Context_setAutoUnfold(x_138);
x_91 = x_139;
x_92 = x_137;
x_93 = x_119;
x_94 = x_118;
x_95 = x_116;
x_96 = x_120;
x_97 = x_112;
x_98 = x_117;
x_99 = x_115;
x_100 = x_111;
x_101 = x_114;
x_102 = x_113;
x_103 = x_140;
goto block_108;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_18);
x_141 = !lean_is_exclusive(x_129);
if (x_141 == 0)
{
return x_129;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_129, 0);
x_143 = lean_ctor_get(x_129, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_129);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
block_171:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = l_Array_append___redArg(x_154, x_167);
lean_dec_ref(x_167);
lean_inc(x_146);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_146);
lean_ctor_set(x_169, 1, x_164);
lean_ctor_set(x_169, 2, x_168);
x_170 = l_Lean_Syntax_node6(x_146, x_147, x_155, x_151, x_157, x_149, x_156, x_169);
x_109 = x_159;
x_110 = x_163;
x_111 = x_152;
x_112 = x_170;
x_113 = x_150;
x_114 = x_162;
x_115 = x_165;
x_116 = x_166;
x_117 = x_161;
x_118 = x_148;
x_119 = x_153;
x_120 = x_160;
x_121 = x_158;
goto block_145;
}
block_199:
{
lean_object* x_193; lean_object* x_194; 
lean_inc_ref(x_180);
x_193 = l_Array_append___redArg(x_180, x_192);
lean_dec_ref(x_192);
lean_inc(x_190);
lean_inc(x_172);
x_194 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_194, 0, x_172);
lean_ctor_set(x_194, 1, x_190);
lean_ctor_set(x_194, 2, x_193);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_195; 
x_195 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
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
x_156 = x_194;
x_157 = x_182;
x_158 = x_183;
x_159 = x_185;
x_160 = x_184;
x_161 = x_186;
x_162 = x_187;
x_163 = x_188;
x_164 = x_190;
x_165 = x_189;
x_166 = x_191;
x_167 = x_195;
goto block_171;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_178, 0);
x_197 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
lean_inc(x_196);
x_198 = lean_array_push(x_197, x_196);
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
x_156 = x_194;
x_157 = x_182;
x_158 = x_183;
x_159 = x_185;
x_160 = x_184;
x_161 = x_186;
x_162 = x_187;
x_163 = x_188;
x_164 = x_190;
x_165 = x_189;
x_166 = x_191;
x_167 = x_198;
goto block_171;
}
}
block_232:
{
lean_object* x_221; lean_object* x_222; 
lean_inc_ref(x_208);
x_221 = l_Array_append___redArg(x_208, x_220);
lean_dec_ref(x_220);
lean_inc(x_218);
lean_inc(x_201);
x_222 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_222, 0, x_201);
lean_ctor_set(x_222, 1, x_218);
lean_ctor_set(x_222, 2, x_221);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_223; 
x_223 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_172 = x_201;
x_173 = x_202;
x_174 = x_203;
x_175 = x_222;
x_176 = x_204;
x_177 = x_205;
x_178 = x_206;
x_179 = x_207;
x_180 = x_208;
x_181 = x_209;
x_182 = x_210;
x_183 = x_211;
x_184 = x_213;
x_185 = x_212;
x_186 = x_214;
x_187 = x_215;
x_188 = x_216;
x_189 = x_217;
x_190 = x_218;
x_191 = x_219;
x_192 = x_223;
goto block_199;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_224 = lean_ctor_get(x_200, 0);
lean_inc(x_224);
lean_dec_ref(x_200);
x_225 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_201);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_201);
lean_ctor_set(x_226, 1, x_225);
lean_inc_ref(x_208);
x_227 = l_Array_append___redArg(x_208, x_224);
lean_dec(x_224);
lean_inc(x_218);
lean_inc(x_201);
x_228 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_228, 0, x_201);
lean_ctor_set(x_228, 1, x_218);
lean_ctor_set(x_228, 2, x_227);
x_229 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_201);
x_230 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_230, 0, x_201);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Array_mkArray3___redArg(x_226, x_228, x_230);
x_172 = x_201;
x_173 = x_202;
x_174 = x_203;
x_175 = x_222;
x_176 = x_204;
x_177 = x_205;
x_178 = x_206;
x_179 = x_207;
x_180 = x_208;
x_181 = x_209;
x_182 = x_210;
x_183 = x_211;
x_184 = x_213;
x_185 = x_212;
x_186 = x_214;
x_187 = x_215;
x_188 = x_216;
x_189 = x_217;
x_190 = x_218;
x_191 = x_219;
x_192 = x_231;
goto block_199;
}
}
block_258:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = l_Array_append___redArg(x_234, x_254);
lean_dec_ref(x_254);
lean_inc(x_252);
x_256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_256, 0, x_252);
lean_ctor_set(x_256, 1, x_243);
lean_ctor_set(x_256, 2, x_255);
x_257 = l_Lean_Syntax_node6(x_252, x_247, x_235, x_238, x_250, x_241, x_236, x_256);
x_109 = x_244;
x_110 = x_249;
x_111 = x_239;
x_112 = x_257;
x_113 = x_237;
x_114 = x_248;
x_115 = x_251;
x_116 = x_253;
x_117 = x_246;
x_118 = x_233;
x_119 = x_240;
x_120 = x_245;
x_121 = x_242;
goto block_145;
}
block_286:
{
lean_object* x_280; lean_object* x_281; 
lean_inc_ref(x_259);
x_280 = l_Array_append___redArg(x_259, x_279);
lean_dec_ref(x_279);
lean_inc(x_267);
lean_inc(x_277);
x_281 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_281, 0, x_277);
lean_ctor_set(x_281, 1, x_267);
lean_ctor_set(x_281, 2, x_280);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_282; 
x_282 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_233 = x_260;
x_234 = x_259;
x_235 = x_261;
x_236 = x_281;
x_237 = x_262;
x_238 = x_263;
x_239 = x_264;
x_240 = x_265;
x_241 = x_266;
x_242 = x_268;
x_243 = x_267;
x_244 = x_269;
x_245 = x_270;
x_246 = x_272;
x_247 = x_271;
x_248 = x_273;
x_249 = x_275;
x_250 = x_274;
x_251 = x_276;
x_252 = x_277;
x_253 = x_278;
x_254 = x_282;
goto block_258;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_264, 0);
x_284 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
lean_inc(x_283);
x_285 = lean_array_push(x_284, x_283);
x_233 = x_260;
x_234 = x_259;
x_235 = x_261;
x_236 = x_281;
x_237 = x_262;
x_238 = x_263;
x_239 = x_264;
x_240 = x_265;
x_241 = x_266;
x_242 = x_268;
x_243 = x_267;
x_244 = x_269;
x_245 = x_270;
x_246 = x_272;
x_247 = x_271;
x_248 = x_273;
x_249 = x_275;
x_250 = x_274;
x_251 = x_276;
x_252 = x_277;
x_253 = x_278;
x_254 = x_285;
goto block_258;
}
}
block_319:
{
lean_object* x_308; lean_object* x_309; 
lean_inc_ref(x_288);
x_308 = l_Array_append___redArg(x_288, x_307);
lean_dec_ref(x_307);
lean_inc(x_295);
lean_inc(x_305);
x_309 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_309, 0, x_305);
lean_ctor_set(x_309, 1, x_295);
lean_ctor_set(x_309, 2, x_308);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_310; 
x_310 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_259 = x_288;
x_260 = x_289;
x_261 = x_290;
x_262 = x_291;
x_263 = x_292;
x_264 = x_293;
x_265 = x_294;
x_266 = x_309;
x_267 = x_295;
x_268 = x_296;
x_269 = x_297;
x_270 = x_298;
x_271 = x_300;
x_272 = x_299;
x_273 = x_301;
x_274 = x_303;
x_275 = x_302;
x_276 = x_304;
x_277 = x_305;
x_278 = x_306;
x_279 = x_310;
goto block_286;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_287, 0);
lean_inc(x_311);
lean_dec_ref(x_287);
x_312 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__4;
lean_inc(x_305);
x_313 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_313, 0, x_305);
lean_ctor_set(x_313, 1, x_312);
lean_inc_ref(x_288);
x_314 = l_Array_append___redArg(x_288, x_311);
lean_dec(x_311);
lean_inc(x_295);
lean_inc(x_305);
x_315 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_315, 0, x_305);
lean_ctor_set(x_315, 1, x_295);
lean_ctor_set(x_315, 2, x_314);
x_316 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__5;
lean_inc(x_305);
x_317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_317, 0, x_305);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Array_mkArray3___redArg(x_313, x_315, x_317);
x_259 = x_288;
x_260 = x_289;
x_261 = x_290;
x_262 = x_291;
x_263 = x_292;
x_264 = x_293;
x_265 = x_294;
x_266 = x_309;
x_267 = x_295;
x_268 = x_296;
x_269 = x_297;
x_270 = x_298;
x_271 = x_300;
x_272 = x_299;
x_273 = x_301;
x_274 = x_303;
x_275 = x_302;
x_276 = x_304;
x_277 = x_305;
x_278 = x_306;
x_279 = x_318;
goto block_286;
}
}
block_351:
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_336 = lean_ctor_get(x_324, 5);
x_337 = l_Lean_SourceInfo_fromRef(x_336, x_335);
x_338 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__1;
x_339 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_338);
x_340 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_341 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_338);
x_342 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_343 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
lean_inc(x_337);
x_344 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_344, 0, x_337);
lean_ctor_set(x_344, 1, x_342);
lean_ctor_set(x_344, 2, x_343);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_345; 
x_345 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_200 = x_320;
x_201 = x_337;
x_202 = x_339;
x_203 = x_321;
x_204 = x_322;
x_205 = x_323;
x_206 = x_325;
x_207 = x_324;
x_208 = x_343;
x_209 = x_341;
x_210 = x_344;
x_211 = x_327;
x_212 = x_328;
x_213 = x_329;
x_214 = x_330;
x_215 = x_331;
x_216 = x_332;
x_217 = x_333;
x_218 = x_342;
x_219 = x_334;
x_220 = x_345;
goto block_232;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_346 = lean_ctor_get(x_326, 0);
lean_inc(x_346);
lean_dec_ref(x_326);
x_347 = l_Lean_SourceInfo_fromRef(x_346, x_3);
lean_dec(x_346);
x_348 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_349 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
x_350 = l_Array_mkArray1___redArg(x_349);
x_200 = x_320;
x_201 = x_337;
x_202 = x_339;
x_203 = x_321;
x_204 = x_322;
x_205 = x_323;
x_206 = x_325;
x_207 = x_324;
x_208 = x_343;
x_209 = x_341;
x_210 = x_344;
x_211 = x_327;
x_212 = x_328;
x_213 = x_329;
x_214 = x_330;
x_215 = x_331;
x_216 = x_332;
x_217 = x_333;
x_218 = x_342;
x_219 = x_334;
x_220 = x_350;
goto block_232;
}
}
block_385:
{
if (lean_obj_tag(x_359) == 0)
{
uint8_t x_367; 
x_367 = 0;
x_320 = x_352;
x_321 = x_353;
x_322 = x_354;
x_323 = x_355;
x_324 = x_356;
x_325 = x_366;
x_326 = x_357;
x_327 = x_358;
x_328 = x_359;
x_329 = x_360;
x_330 = x_361;
x_331 = x_362;
x_332 = x_363;
x_333 = x_364;
x_334 = x_365;
x_335 = x_367;
goto block_351;
}
else
{
if (x_363 == 0)
{
x_320 = x_352;
x_321 = x_353;
x_322 = x_354;
x_323 = x_355;
x_324 = x_356;
x_325 = x_366;
x_326 = x_357;
x_327 = x_358;
x_328 = x_359;
x_329 = x_360;
x_330 = x_361;
x_331 = x_362;
x_332 = x_363;
x_333 = x_364;
x_334 = x_365;
x_335 = x_363;
goto block_351;
}
else
{
lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_368 = lean_ctor_get(x_356, 5);
x_369 = 0;
x_370 = l_Lean_SourceInfo_fromRef(x_368, x_369);
x_371 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__2;
x_372 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_371);
x_373 = l_Lean_SourceInfo_fromRef(x_18, x_3);
x_374 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__3;
x_375 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__9;
x_377 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__10;
lean_inc(x_370);
x_378 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_378, 0, x_370);
lean_ctor_set(x_378, 1, x_376);
lean_ctor_set(x_378, 2, x_377);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_379; 
x_379 = l_Lean_Elab_Tactic_evalSimpTrace___lam__0___closed__0;
x_287 = x_352;
x_288 = x_377;
x_289 = x_353;
x_290 = x_375;
x_291 = x_354;
x_292 = x_355;
x_293 = x_366;
x_294 = x_356;
x_295 = x_376;
x_296 = x_358;
x_297 = x_359;
x_298 = x_360;
x_299 = x_361;
x_300 = x_372;
x_301 = x_362;
x_302 = x_363;
x_303 = x_378;
x_304 = x_364;
x_305 = x_370;
x_306 = x_365;
x_307 = x_379;
goto block_319;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_380 = lean_ctor_get(x_357, 0);
lean_inc(x_380);
lean_dec_ref(x_357);
x_381 = l_Lean_SourceInfo_fromRef(x_380, x_3);
lean_dec(x_380);
x_382 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__6;
x_383 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = l_Array_mkArray1___redArg(x_383);
x_287 = x_352;
x_288 = x_377;
x_289 = x_353;
x_290 = x_375;
x_291 = x_354;
x_292 = x_355;
x_293 = x_366;
x_294 = x_356;
x_295 = x_376;
x_296 = x_358;
x_297 = x_359;
x_298 = x_360;
x_299 = x_361;
x_300 = x_372;
x_301 = x_362;
x_302 = x_363;
x_303 = x_378;
x_304 = x_364;
x_305 = x_370;
x_306 = x_365;
x_307 = x_384;
goto block_319;
}
}
}
}
block_408:
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_unsigned_to_nat(3u);
x_402 = l_Lean_Syntax_getArg(x_390, x_401);
lean_dec(x_390);
x_403 = l_Lean_Syntax_getOptional_x3f(x_402);
lean_dec(x_402);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
x_404 = lean_box(0);
x_352 = x_391;
x_353 = x_397;
x_354 = x_392;
x_355 = x_388;
x_356 = x_398;
x_357 = x_389;
x_358 = x_400;
x_359 = x_386;
x_360 = x_399;
x_361 = x_396;
x_362 = x_393;
x_363 = x_387;
x_364 = x_394;
x_365 = x_395;
x_366 = x_404;
goto block_385;
}
else
{
uint8_t x_405; 
x_405 = !lean_is_exclusive(x_403);
if (x_405 == 0)
{
x_352 = x_391;
x_353 = x_397;
x_354 = x_392;
x_355 = x_388;
x_356 = x_398;
x_357 = x_389;
x_358 = x_400;
x_359 = x_386;
x_360 = x_399;
x_361 = x_396;
x_362 = x_393;
x_363 = x_387;
x_364 = x_394;
x_365 = x_395;
x_366 = x_403;
goto block_385;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
lean_dec(x_403);
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_406);
x_352 = x_391;
x_353 = x_397;
x_354 = x_392;
x_355 = x_388;
x_356 = x_398;
x_357 = x_389;
x_358 = x_400;
x_359 = x_386;
x_360 = x_399;
x_361 = x_396;
x_362 = x_393;
x_363 = x_387;
x_364 = x_394;
x_365 = x_395;
x_366 = x_407;
goto block_385;
}
}
}
block_438:
{
lean_object* x_425; uint8_t x_426; 
x_425 = l_Lean_Syntax_getArg(x_414, x_412);
x_426 = l_Lean_Syntax_isNone(x_425);
if (x_426 == 0)
{
uint8_t x_427; 
lean_inc(x_425);
x_427 = l_Lean_Syntax_matchesNull(x_425, x_409);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_425);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec_ref(x_420);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_410);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_428 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_424);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
x_429 = l_Lean_Syntax_getArg(x_425, x_17);
lean_dec(x_425);
x_430 = l_Lean_Elab_Tactic_evalSimpAllTrace___lam__0___closed__12;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_431 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_430);
lean_inc(x_429);
x_432 = l_Lean_Syntax_isOfKind(x_429, x_431);
lean_dec(x_431);
if (x_432 == 0)
{
lean_object* x_433; 
lean_dec(x_429);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec_ref(x_420);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_410);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_433 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_424);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = l_Lean_Syntax_getArg(x_429, x_409);
lean_dec(x_429);
x_435 = l_Lean_Syntax_getArgs(x_434);
lean_dec(x_434);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
x_386 = x_410;
x_387 = x_411;
x_388 = x_413;
x_389 = x_415;
x_390 = x_414;
x_391 = x_436;
x_392 = x_416;
x_393 = x_417;
x_394 = x_418;
x_395 = x_419;
x_396 = x_420;
x_397 = x_421;
x_398 = x_422;
x_399 = x_423;
x_400 = x_424;
goto block_408;
}
}
}
else
{
lean_object* x_437; 
lean_dec(x_425);
x_437 = lean_box(0);
x_386 = x_410;
x_387 = x_411;
x_388 = x_413;
x_389 = x_415;
x_390 = x_414;
x_391 = x_437;
x_392 = x_416;
x_393 = x_417;
x_394 = x_418;
x_395 = x_419;
x_396 = x_420;
x_397 = x_421;
x_398 = x_422;
x_399 = x_423;
x_400 = x_424;
goto block_408;
}
}
block_467:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_449 = lean_unsigned_to_nat(2u);
x_450 = l_Lean_Syntax_getArg(x_2, x_449);
x_451 = l_Lean_Elab_Tactic_evalDSimpTrace___lam__0___closed__4;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_452 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_451);
lean_inc(x_450);
x_453 = l_Lean_Syntax_isOfKind(x_450, x_452);
lean_dec(x_452);
if (x_453 == 0)
{
lean_object* x_454; 
lean_dec(x_450);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_454 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_448);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_455 = l_Lean_Syntax_getArg(x_450, x_17);
x_456 = l_Lean_Elab_Tactic_evalSimpTrace___lam__2___closed__15;
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_457 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_456);
lean_inc(x_455);
x_458 = l_Lean_Syntax_isOfKind(x_455, x_457);
lean_dec(x_457);
if (x_458 == 0)
{
lean_object* x_459; 
lean_dec(x_455);
lean_dec(x_450);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_459 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_448);
return x_459;
}
else
{
lean_object* x_460; uint8_t x_461; 
x_460 = l_Lean_Syntax_getArg(x_450, x_409);
x_461 = l_Lean_Syntax_isNone(x_460);
if (x_461 == 0)
{
uint8_t x_462; 
lean_inc(x_460);
x_462 = l_Lean_Syntax_matchesNull(x_460, x_409);
if (x_462 == 0)
{
lean_object* x_463; 
lean_dec(x_460);
lean_dec(x_455);
lean_dec(x_450);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec_ref(x_444);
lean_dec(x_443);
lean_dec_ref(x_442);
lean_dec(x_441);
lean_dec_ref(x_440);
lean_dec(x_439);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_463 = l_Lean_Elab_throwUnsupportedSyntax___at___Lean_Elab_Tactic_evalSimpTrace_spec__0___redArg(x_448);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; 
x_464 = l_Lean_Syntax_getArg(x_460, x_17);
lean_dec(x_460);
x_465 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_465, 0, x_464);
x_410 = x_439;
x_411 = x_458;
x_412 = x_449;
x_413 = x_455;
x_414 = x_450;
x_415 = x_465;
x_416 = x_440;
x_417 = x_441;
x_418 = x_442;
x_419 = x_443;
x_420 = x_444;
x_421 = x_445;
x_422 = x_446;
x_423 = x_447;
x_424 = x_448;
goto block_438;
}
}
else
{
lean_object* x_466; 
lean_dec(x_460);
x_466 = lean_box(0);
x_410 = x_439;
x_411 = x_458;
x_412 = x_449;
x_413 = x_455;
x_414 = x_450;
x_415 = x_466;
x_416 = x_440;
x_417 = x_441;
x_418 = x_442;
x_419 = x_443;
x_420 = x_444;
x_421 = x_445;
x_422 = x_446;
x_423 = x_447;
x_424 = x_448;
goto block_438;
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
