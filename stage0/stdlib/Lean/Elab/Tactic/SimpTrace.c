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
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__2;
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__6;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__3;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1;
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1;
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__13;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withSimpDiagnostics(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__15;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__4;
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__3;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__1;
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___boxed(lean_object**);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__3;
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__3;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__8;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__2;
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
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg), 1, 0);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_2 = 1;
x_3 = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2;
x_15 = l_Lean_Elab_Tactic_simpLocation(x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = l_Lean_Elab_Tactic_expandLocation(x_16);
x_18 = l_Lean_Elab_Tactic_simpLocation(x_2, x_3, x_4, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getSimpTheorems___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = 0;
x_15 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Elab_Tactic_mkSimpContext(x_3, x_13, x_14, x_13, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___boxed), 13, 3);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Elab_Tactic_mkSimpCallStx(x_3, x_26, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_10, 5);
lean_inc(x_30);
x_31 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_33);
lean_ctor_set(x_34, 5, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_36 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_37 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_2, x_34, x_35, x_36, x_33, x_8, x_9, x_10, x_11, x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_dec(x_24);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_dec(x_24);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_24);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
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
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
return x_27;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_27, 0);
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_27);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_23);
if (x_52 == 0)
{
return x_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_23);
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
x_56 = !lean_is_exclusive(x_16);
if (x_56 == 0)
{
return x_16;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_16, 0);
x_58 = lean_ctor_get(x_16, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_16);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("only", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAutoUnfold", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__13;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp!", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getOptional_x3f(x_19);
lean_dec(x_19);
x_21 = l_Lean_Syntax_getOptional_x3f(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_270; 
x_270 = lean_box(0);
x_22 = x_270;
goto block_269;
}
else
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_20);
if (x_271 == 0)
{
x_22 = x_20;
goto block_269;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_20, 0);
lean_inc(x_272);
lean_dec(x_20);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
x_22 = x_273;
goto block_269;
}
}
block_269:
{
lean_object* x_23; 
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_265; 
x_265 = lean_box(0);
x_23 = x_265;
goto block_264;
}
else
{
uint8_t x_266; 
x_266 = !lean_is_exclusive(x_21);
if (x_266 == 0)
{
x_23 = x_21;
goto block_264;
}
else
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_21, 0);
lean_inc(x_267);
lean_dec(x_21);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_267);
x_23 = x_268;
goto block_264;
}
}
block_264:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_15, 5);
lean_inc(x_24);
x_25 = 0;
x_26 = l_Lean_SourceInfo_fromRef(x_24, x_25);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_16, x_17);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = l_Lean_SourceInfo_fromRef(x_3, x_31);
x_33 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4;
lean_ctor_set_tag(x_27, 2);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_32);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_83; 
x_83 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_34 = x_83;
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_23, 0);
lean_inc(x_84);
lean_dec(x_23);
x_85 = l_Array_mkArray1___rarg(x_84);
x_34 = x_85;
goto block_82;
}
block_82:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_36 = l_Array_append___rarg(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_26);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_36);
if (lean_obj_tag(x_6) == 0)
{
x_39 = x_35;
goto block_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_6, 0);
x_78 = l_Lean_SourceInfo_fromRef(x_77, x_31);
x_79 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Array_mkArray1___rarg(x_80);
x_39 = x_81;
goto block_76;
}
block_76:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Array_append___rarg(x_35, x_39);
lean_dec(x_39);
lean_inc(x_26);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_40);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_26);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_42);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
lean_inc(x_43);
x_45 = l_Lean_Syntax_node6(x_26, x_44, x_27, x_5, x_38, x_41, x_43, x_43);
x_46 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_45, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_29);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
x_48 = lean_array_push(x_35, x_47);
x_49 = l_Array_append___rarg(x_35, x_48);
lean_dec(x_48);
lean_inc(x_26);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_26);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_49);
x_51 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_52 = l_Lean_Syntax_node6(x_26, x_51, x_27, x_5, x_38, x_41, x_43, x_50);
x_53 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_52, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_29);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_8, 0);
x_55 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_26);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_26);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_append___rarg(x_35, x_54);
lean_inc(x_26);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_37);
lean_ctor_set(x_58, 2, x_57);
x_59 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_26);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_26);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_mkArray3___rarg(x_56, x_58, x_60);
x_62 = l_Array_append___rarg(x_35, x_61);
lean_dec(x_61);
lean_inc(x_26);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_37);
lean_ctor_set(x_63, 2, x_62);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_26);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_26);
lean_ctor_set(x_65, 1, x_37);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_67 = l_Lean_Syntax_node6(x_26, x_66, x_27, x_5, x_38, x_41, x_63, x_65);
x_68 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_29);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_22, 0);
lean_inc(x_69);
x_70 = lean_array_push(x_35, x_69);
x_71 = l_Array_append___rarg(x_35, x_70);
lean_dec(x_70);
lean_inc(x_26);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_26);
lean_ctor_set(x_72, 1, x_37);
lean_ctor_set(x_72, 2, x_71);
x_73 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_74 = l_Lean_Syntax_node6(x_26, x_73, x_27, x_5, x_38, x_41, x_63, x_72);
x_75 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_74, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_29);
return x_75;
}
}
}
}
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_27, 1);
lean_inc(x_86);
lean_dec(x_27);
x_87 = 1;
x_88 = l_Lean_SourceInfo_fromRef(x_3, x_87);
x_89 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4;
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_140; 
x_140 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_91 = x_140;
goto block_139;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_23, 0);
lean_inc(x_141);
lean_dec(x_23);
x_142 = l_Array_mkArray1___rarg(x_141);
x_91 = x_142;
goto block_139;
}
block_139:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_93 = l_Array_append___rarg(x_92, x_91);
lean_dec(x_91);
x_94 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_26);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_26);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_93);
if (lean_obj_tag(x_6) == 0)
{
x_96 = x_92;
goto block_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_6, 0);
x_135 = l_Lean_SourceInfo_fromRef(x_134, x_87);
x_136 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_137 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Array_mkArray1___rarg(x_137);
x_96 = x_138;
goto block_133;
}
block_133:
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Array_append___rarg(x_92, x_96);
lean_dec(x_96);
lean_inc(x_26);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_26);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_97);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_26);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_26);
lean_ctor_set(x_100, 1, x_94);
lean_ctor_set(x_100, 2, x_99);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
lean_inc(x_100);
x_102 = l_Lean_Syntax_node6(x_26, x_101, x_90, x_5, x_95, x_98, x_100, x_100);
x_103 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_102, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_86);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_22, 0);
lean_inc(x_104);
x_105 = lean_array_push(x_92, x_104);
x_106 = l_Array_append___rarg(x_92, x_105);
lean_dec(x_105);
lean_inc(x_26);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_26);
lean_ctor_set(x_107, 1, x_94);
lean_ctor_set(x_107, 2, x_106);
x_108 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_109 = l_Lean_Syntax_node6(x_26, x_108, x_90, x_5, x_95, x_98, x_100, x_107);
x_110 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_109, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_86);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_111 = lean_ctor_get(x_8, 0);
x_112 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_26);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_26);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Array_append___rarg(x_92, x_111);
lean_inc(x_26);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_26);
lean_ctor_set(x_115, 1, x_94);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_26);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_mkArray3___rarg(x_113, x_115, x_117);
x_119 = l_Array_append___rarg(x_92, x_118);
lean_dec(x_118);
lean_inc(x_26);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_26);
lean_ctor_set(x_120, 1, x_94);
lean_ctor_set(x_120, 2, x_119);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_26);
x_122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_122, 0, x_26);
lean_ctor_set(x_122, 1, x_94);
lean_ctor_set(x_122, 2, x_121);
x_123 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_124 = l_Lean_Syntax_node6(x_26, x_123, x_90, x_5, x_95, x_98, x_120, x_122);
x_125 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_124, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_86);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_22, 0);
lean_inc(x_126);
x_127 = lean_array_push(x_92, x_126);
x_128 = l_Array_append___rarg(x_92, x_127);
lean_dec(x_127);
lean_inc(x_26);
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_26);
lean_ctor_set(x_129, 1, x_94);
lean_ctor_set(x_129, 2, x_128);
x_130 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_131 = l_Lean_Syntax_node6(x_26, x_130, x_90, x_5, x_95, x_98, x_120, x_129);
x_132 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_131, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_86);
return x_132;
}
}
}
}
}
}
else
{
lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_15, 5);
lean_inc(x_143);
x_144 = 0;
x_145 = l_Lean_SourceInfo_fromRef(x_143, x_144);
lean_dec(x_143);
x_146 = lean_st_ref_get(x_16, x_17);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_146, 1);
x_149 = lean_ctor_get(x_146, 0);
lean_dec(x_149);
x_150 = 1;
x_151 = l_Lean_SourceInfo_fromRef(x_3, x_150);
x_152 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__15;
lean_ctor_set_tag(x_146, 2);
lean_ctor_set(x_146, 1, x_152);
lean_ctor_set(x_146, 0, x_151);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_202; 
x_202 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_153 = x_202;
goto block_201;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_23, 0);
lean_inc(x_203);
lean_dec(x_23);
x_204 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_205 = lean_array_push(x_204, x_203);
x_153 = x_205;
goto block_201;
}
block_201:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_155 = l_Array_append___rarg(x_154, x_153);
lean_dec(x_153);
x_156 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_145);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_155);
if (lean_obj_tag(x_6) == 0)
{
x_158 = x_154;
goto block_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_6, 0);
x_197 = l_Lean_SourceInfo_fromRef(x_196, x_150);
x_198 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Array_mkArray1___rarg(x_199);
x_158 = x_200;
goto block_195;
}
block_195:
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Array_append___rarg(x_154, x_158);
lean_dec(x_158);
lean_inc(x_145);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_145);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_159);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_145);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_145);
lean_ctor_set(x_162, 1, x_156);
lean_ctor_set(x_162, 2, x_161);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
lean_inc(x_162);
x_164 = l_Lean_Syntax_node6(x_145, x_163, x_146, x_5, x_157, x_160, x_162, x_162);
x_165 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_164, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_148);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_22, 0);
lean_inc(x_166);
x_167 = lean_array_push(x_154, x_166);
x_168 = l_Array_append___rarg(x_154, x_167);
lean_dec(x_167);
lean_inc(x_145);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_145);
lean_ctor_set(x_169, 1, x_156);
lean_ctor_set(x_169, 2, x_168);
x_170 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
x_171 = l_Lean_Syntax_node6(x_145, x_170, x_146, x_5, x_157, x_160, x_162, x_169);
x_172 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_171, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_148);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_173 = lean_ctor_get(x_8, 0);
x_174 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_145);
x_175 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_175, 0, x_145);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Array_append___rarg(x_154, x_173);
lean_inc(x_145);
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_145);
lean_ctor_set(x_177, 1, x_156);
lean_ctor_set(x_177, 2, x_176);
x_178 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_145);
x_179 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_179, 0, x_145);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Array_mkArray3___rarg(x_175, x_177, x_179);
x_181 = l_Array_append___rarg(x_154, x_180);
lean_dec(x_180);
lean_inc(x_145);
x_182 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_182, 0, x_145);
lean_ctor_set(x_182, 1, x_156);
lean_ctor_set(x_182, 2, x_181);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_145);
x_184 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_184, 0, x_145);
lean_ctor_set(x_184, 1, x_156);
lean_ctor_set(x_184, 2, x_183);
x_185 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
x_186 = l_Lean_Syntax_node6(x_145, x_185, x_146, x_5, x_157, x_160, x_182, x_184);
x_187 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_186, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_148);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_188 = lean_ctor_get(x_22, 0);
lean_inc(x_188);
x_189 = lean_array_push(x_154, x_188);
x_190 = l_Array_append___rarg(x_154, x_189);
lean_dec(x_189);
lean_inc(x_145);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_145);
lean_ctor_set(x_191, 1, x_156);
lean_ctor_set(x_191, 2, x_190);
x_192 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
x_193 = l_Lean_Syntax_node6(x_145, x_192, x_146, x_5, x_157, x_160, x_182, x_191);
x_194 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_193, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_148);
return x_194;
}
}
}
}
}
else
{
lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_206 = lean_ctor_get(x_146, 1);
lean_inc(x_206);
lean_dec(x_146);
x_207 = 1;
x_208 = l_Lean_SourceInfo_fromRef(x_3, x_207);
x_209 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__15;
x_210 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_260; 
x_260 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_211 = x_260;
goto block_259;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_23, 0);
lean_inc(x_261);
lean_dec(x_23);
x_262 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_263 = lean_array_push(x_262, x_261);
x_211 = x_263;
goto block_259;
}
block_259:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_213 = l_Array_append___rarg(x_212, x_211);
lean_dec(x_211);
x_214 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_145);
x_215 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_215, 0, x_145);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set(x_215, 2, x_213);
if (lean_obj_tag(x_6) == 0)
{
x_216 = x_212;
goto block_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_254 = lean_ctor_get(x_6, 0);
x_255 = l_Lean_SourceInfo_fromRef(x_254, x_207);
x_256 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_257 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Array_mkArray1___rarg(x_257);
x_216 = x_258;
goto block_253;
}
block_253:
{
lean_object* x_217; lean_object* x_218; 
x_217 = l_Array_append___rarg(x_212, x_216);
lean_dec(x_216);
lean_inc(x_145);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_145);
lean_ctor_set(x_218, 1, x_214);
lean_ctor_set(x_218, 2, x_217);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_145);
x_220 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_220, 0, x_145);
lean_ctor_set(x_220, 1, x_214);
lean_ctor_set(x_220, 2, x_219);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
lean_inc(x_220);
x_222 = l_Lean_Syntax_node6(x_145, x_221, x_210, x_5, x_215, x_218, x_220, x_220);
x_223 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_222, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_206);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_22, 0);
lean_inc(x_224);
x_225 = lean_array_push(x_212, x_224);
x_226 = l_Array_append___rarg(x_212, x_225);
lean_dec(x_225);
lean_inc(x_145);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_145);
lean_ctor_set(x_227, 1, x_214);
lean_ctor_set(x_227, 2, x_226);
x_228 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
x_229 = l_Lean_Syntax_node6(x_145, x_228, x_210, x_5, x_215, x_218, x_220, x_227);
x_230 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_229, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_206);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_231 = lean_ctor_get(x_8, 0);
x_232 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_145);
x_233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_233, 0, x_145);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Array_append___rarg(x_212, x_231);
lean_inc(x_145);
x_235 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_235, 0, x_145);
lean_ctor_set(x_235, 1, x_214);
lean_ctor_set(x_235, 2, x_234);
x_236 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_145);
x_237 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_237, 0, x_145);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Array_mkArray3___rarg(x_233, x_235, x_237);
x_239 = l_Array_append___rarg(x_212, x_238);
lean_dec(x_238);
lean_inc(x_145);
x_240 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_240, 0, x_145);
lean_ctor_set(x_240, 1, x_214);
lean_ctor_set(x_240, 2, x_239);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_145);
x_242 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_242, 0, x_145);
lean_ctor_set(x_242, 1, x_214);
lean_ctor_set(x_242, 2, x_241);
x_243 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
x_244 = l_Lean_Syntax_node6(x_145, x_243, x_210, x_5, x_215, x_218, x_240, x_242);
x_245 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_244, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_206);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_22, 0);
lean_inc(x_246);
x_247 = lean_array_push(x_212, x_246);
x_248 = l_Array_append___rarg(x_212, x_247);
lean_dec(x_247);
lean_inc(x_145);
x_249 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_249, 0, x_145);
lean_ctor_set(x_249, 1, x_214);
lean_ctor_set(x_249, 2, x_248);
x_250 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14;
x_251 = l_Lean_Syntax_node6(x_145, x_250, x_210, x_5, x_215, x_218, x_240, x_249);
x_252 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_22, x_3, x_251, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_206);
return x_252;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpArgs", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_18);
x_21 = l_Lean_Syntax_matchesNull(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_25 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_16);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = l_Lean_Syntax_getArg(x_24, x_20);
lean_dec(x_24);
x_29 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_7, x_31, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_18);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_7, x_34, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpTraceArgsRest", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
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
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
x_21 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4;
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_15, x_24);
x_26 = l_Lean_Syntax_getArg(x_15, x_14);
x_27 = l_Lean_Syntax_isNone(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_inc(x_26);
x_28 = l_Lean_Syntax_matchesNull(x_26, x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Syntax_getArg(x_26, x_19);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4(x_15, x_25, x_2, x_4, x_20, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_15);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4(x_15, x_25, x_2, x_4, x_20, x_35, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_25);
lean_dec(x_15);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpTrace", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_14 = l_Lean_Elab_Tactic_withMainContext___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_18);
x_20 = l_Lean_Syntax_matchesNull(x_18, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
x_21 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_22 = l_Lean_Elab_Tactic_withMainContext___rarg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Syntax_getArg(x_18, x_15);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___boxed), 13, 4);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_16);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l_Lean_Elab_Tactic_withMainContext___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___boxed), 13, 4);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_16);
lean_closure_set(x_31, 2, x_30);
lean_closure_set(x_31, 3, x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_Tactic_withMainContext___rarg(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpTrace", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(40u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(45u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l_Lean_Elab_Tactic_mkSimpCallStx(x_2, x_14, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_11, 5);
lean_inc(x_18);
x_19 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_22, 4, x_21);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_24 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_25 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_22, x_23, x_24, x_21, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5;
x_3 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4;
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
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2;
x_2 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__6;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__3;
x_2 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Tactic_mkSimpContext(x_2, x_12, x_13, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_24 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__8;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_simpAll(x_20, x_18, x_23, x_24, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Elab_Tactic_replaceMainGoal(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(x_29, x_2, x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_31);
lean_dec(x_29);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_dec(x_25);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_26, 1);
x_41 = lean_ctor_get(x_26, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_27, 0);
lean_inc(x_42);
lean_dec(x_27);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 0, x_42);
x_43 = l_Lean_Elab_Tactic_replaceMainGoal(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(x_40, x_2, x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_44);
lean_dec(x_40);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_26, 1);
lean_inc(x_51);
lean_dec(x_26);
x_52 = lean_ctor_get(x_27, 0);
lean_inc(x_52);
lean_dec(x_27);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_22);
x_54 = l_Lean_Elab_Tactic_replaceMainGoal(x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(x_51, x_2, x_1, x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_55);
lean_dec(x_51);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_25);
if (x_62 == 0)
{
return x_25;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_25, 0);
x_64 = lean_ctor_get(x_25, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_25);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_19);
if (x_66 == 0)
{
return x_19;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_19, 0);
x_68 = lean_ctor_get(x_19, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_19);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_15);
if (x_70 == 0)
{
return x_15;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_15, 0);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_15);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAll", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_all", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAllAutoUnfold", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp_all!", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Syntax_getOptional_x3f(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_262; 
x_262 = lean_box(0);
x_18 = x_262;
goto block_261;
}
else
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_17);
if (x_263 == 0)
{
x_18 = x_17;
goto block_261;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_17, 0);
lean_inc(x_264);
lean_dec(x_17);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_18 = x_265;
goto block_261;
}
}
block_261:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_14, 5);
lean_inc(x_19);
x_20 = 0;
x_21 = l_Lean_SourceInfo_fromRef(x_19, x_20);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_15, x_16);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = l_Lean_SourceInfo_fromRef(x_2, x_26);
x_28 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3;
lean_ctor_set_tag(x_22, 2);
lean_ctor_set(x_22, 1, x_28);
lean_ctor_set(x_22, 0, x_27);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_78; 
x_78 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_29 = x_78;
goto block_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_18, 0);
lean_inc(x_79);
lean_dec(x_18);
x_80 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_81 = lean_array_push(x_80, x_79);
x_29 = x_81;
goto block_77;
}
block_77:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_31 = l_Array_append___rarg(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_21);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_31);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_21);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
lean_inc(x_35);
x_37 = l_Lean_Syntax_node5(x_21, x_36, x_22, x_5, x_33, x_35, x_35);
x_38 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_21);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Array_append___rarg(x_30, x_39);
lean_inc(x_21);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_42);
x_44 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_21);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Array_mkArray3___rarg(x_41, x_43, x_45);
x_47 = l_Array_append___rarg(x_30, x_46);
lean_dec(x_46);
lean_inc(x_21);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_32);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_50 = l_Lean_Syntax_node5(x_21, x_49, x_22, x_5, x_33, x_35, x_48);
x_51 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_50, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = l_Lean_SourceInfo_fromRef(x_52, x_26);
x_54 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_mkArray1___rarg(x_55);
x_57 = l_Array_append___rarg(x_30, x_56);
lean_dec(x_56);
lean_inc(x_21);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_32);
lean_ctor_set(x_58, 2, x_57);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_21);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_21);
lean_ctor_set(x_60, 1, x_32);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_62 = l_Lean_Syntax_node5(x_21, x_61, x_22, x_5, x_33, x_58, x_60);
x_63 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_64 = lean_ctor_get(x_7, 0);
x_65 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_21);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_21);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Array_append___rarg(x_30, x_64);
lean_inc(x_21);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_21);
lean_ctor_set(x_68, 1, x_32);
lean_ctor_set(x_68, 2, x_67);
x_69 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_21);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_21);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Array_mkArray3___rarg(x_66, x_68, x_70);
x_72 = l_Array_append___rarg(x_30, x_71);
lean_dec(x_71);
lean_inc(x_21);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_21);
lean_ctor_set(x_73, 1, x_32);
lean_ctor_set(x_73, 2, x_72);
x_74 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_75 = l_Lean_Syntax_node5(x_21, x_74, x_22, x_5, x_33, x_58, x_73);
x_76 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_75, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
return x_76;
}
}
}
}
else
{
lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_22, 1);
lean_inc(x_82);
lean_dec(x_22);
x_83 = 1;
x_84 = l_Lean_SourceInfo_fromRef(x_2, x_83);
x_85 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3;
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_136; 
x_136 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_87 = x_136;
goto block_135;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_18, 0);
lean_inc(x_137);
lean_dec(x_18);
x_138 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_139 = lean_array_push(x_138, x_137);
x_87 = x_139;
goto block_135;
}
block_135:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_89 = l_Array_append___rarg(x_88, x_87);
lean_dec(x_87);
x_90 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_21);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_21);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_89);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_21);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_21);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_92);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
lean_inc(x_93);
x_95 = l_Lean_Syntax_node5(x_21, x_94, x_86, x_5, x_91, x_93, x_93);
x_96 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_95, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_82);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_7, 0);
x_98 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_21);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_21);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Array_append___rarg(x_88, x_97);
lean_inc(x_21);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_21);
lean_ctor_set(x_101, 1, x_90);
lean_ctor_set(x_101, 2, x_100);
x_102 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_21);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_21);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Array_mkArray3___rarg(x_99, x_101, x_103);
x_105 = l_Array_append___rarg(x_88, x_104);
lean_dec(x_104);
lean_inc(x_21);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_21);
lean_ctor_set(x_106, 1, x_90);
lean_ctor_set(x_106, 2, x_105);
x_107 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_108 = l_Lean_Syntax_node5(x_21, x_107, x_86, x_5, x_91, x_93, x_106);
x_109 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_108, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_82);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_4, 0);
x_111 = l_Lean_SourceInfo_fromRef(x_110, x_83);
x_112 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Array_mkArray1___rarg(x_113);
x_115 = l_Array_append___rarg(x_88, x_114);
lean_dec(x_114);
lean_inc(x_21);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_21);
lean_ctor_set(x_116, 1, x_90);
lean_ctor_set(x_116, 2, x_115);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_21);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_21);
lean_ctor_set(x_118, 1, x_90);
lean_ctor_set(x_118, 2, x_117);
x_119 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_120 = l_Lean_Syntax_node5(x_21, x_119, x_86, x_5, x_91, x_116, x_118);
x_121 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_120, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_82);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_122 = lean_ctor_get(x_7, 0);
x_123 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_21);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_21);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Array_append___rarg(x_88, x_122);
lean_inc(x_21);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_21);
lean_ctor_set(x_126, 1, x_90);
lean_ctor_set(x_126, 2, x_125);
x_127 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_21);
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_21);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Array_mkArray3___rarg(x_124, x_126, x_128);
x_130 = l_Array_append___rarg(x_88, x_129);
lean_dec(x_129);
lean_inc(x_21);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_21);
lean_ctor_set(x_131, 1, x_90);
lean_ctor_set(x_131, 2, x_130);
x_132 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_133 = l_Lean_Syntax_node5(x_21, x_132, x_86, x_5, x_91, x_116, x_131);
x_134 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_133, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_82);
return x_134;
}
}
}
}
}
else
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_14, 5);
lean_inc(x_140);
x_141 = 0;
x_142 = l_Lean_SourceInfo_fromRef(x_140, x_141);
lean_dec(x_140);
x_143 = lean_st_ref_get(x_15, x_16);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_143, 1);
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
x_147 = 1;
x_148 = l_Lean_SourceInfo_fromRef(x_2, x_147);
x_149 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6;
lean_ctor_set_tag(x_143, 2);
lean_ctor_set(x_143, 1, x_149);
lean_ctor_set(x_143, 0, x_148);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_199; 
x_199 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_150 = x_199;
goto block_198;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_18, 0);
lean_inc(x_200);
lean_dec(x_18);
x_201 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_202 = lean_array_push(x_201, x_200);
x_150 = x_202;
goto block_198;
}
block_198:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_152 = l_Array_append___rarg(x_151, x_150);
lean_dec(x_150);
x_153 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_142);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_142);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_152);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_142);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_142);
lean_ctor_set(x_156, 1, x_153);
lean_ctor_set(x_156, 2, x_155);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
lean_inc(x_156);
x_158 = l_Lean_Syntax_node5(x_142, x_157, x_143, x_5, x_154, x_156, x_156);
x_159 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_158, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_145);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_160 = lean_ctor_get(x_7, 0);
x_161 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_142);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_142);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Array_append___rarg(x_151, x_160);
lean_inc(x_142);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_142);
lean_ctor_set(x_164, 1, x_153);
lean_ctor_set(x_164, 2, x_163);
x_165 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_142);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_142);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Array_mkArray3___rarg(x_162, x_164, x_166);
x_168 = l_Array_append___rarg(x_151, x_167);
lean_dec(x_167);
lean_inc(x_142);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_142);
lean_ctor_set(x_169, 1, x_153);
lean_ctor_set(x_169, 2, x_168);
x_170 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_171 = l_Lean_Syntax_node5(x_142, x_170, x_143, x_5, x_154, x_156, x_169);
x_172 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_171, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_145);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_4, 0);
x_174 = l_Lean_SourceInfo_fromRef(x_173, x_147);
x_175 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = l_Array_mkArray1___rarg(x_176);
x_178 = l_Array_append___rarg(x_151, x_177);
lean_dec(x_177);
lean_inc(x_142);
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_142);
lean_ctor_set(x_179, 1, x_153);
lean_ctor_set(x_179, 2, x_178);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_142);
x_181 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_181, 0, x_142);
lean_ctor_set(x_181, 1, x_153);
lean_ctor_set(x_181, 2, x_180);
x_182 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_183 = l_Lean_Syntax_node5(x_142, x_182, x_143, x_5, x_154, x_179, x_181);
x_184 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_183, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_145);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_185 = lean_ctor_get(x_7, 0);
x_186 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_142);
x_187 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_187, 0, x_142);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Array_append___rarg(x_151, x_185);
lean_inc(x_142);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_142);
lean_ctor_set(x_189, 1, x_153);
lean_ctor_set(x_189, 2, x_188);
x_190 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_142);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_142);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Array_mkArray3___rarg(x_187, x_189, x_191);
x_193 = l_Array_append___rarg(x_151, x_192);
lean_dec(x_192);
lean_inc(x_142);
x_194 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_194, 0, x_142);
lean_ctor_set(x_194, 1, x_153);
lean_ctor_set(x_194, 2, x_193);
x_195 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_196 = l_Lean_Syntax_node5(x_142, x_195, x_143, x_5, x_154, x_179, x_194);
x_197 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_196, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_145);
return x_197;
}
}
}
}
else
{
lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_143, 1);
lean_inc(x_203);
lean_dec(x_143);
x_204 = 1;
x_205 = l_Lean_SourceInfo_fromRef(x_2, x_204);
x_206 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6;
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_257; 
x_257 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_208 = x_257;
goto block_256;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_18, 0);
lean_inc(x_258);
lean_dec(x_18);
x_259 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_260 = lean_array_push(x_259, x_258);
x_208 = x_260;
goto block_256;
}
block_256:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
x_210 = l_Array_append___rarg(x_209, x_208);
lean_dec(x_208);
x_211 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_142);
x_212 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_212, 0, x_142);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_210);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_142);
x_214 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_214, 0, x_142);
lean_ctor_set(x_214, 1, x_211);
lean_ctor_set(x_214, 2, x_213);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
lean_inc(x_214);
x_216 = l_Lean_Syntax_node5(x_142, x_215, x_207, x_5, x_212, x_214, x_214);
x_217 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_216, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_203);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_218 = lean_ctor_get(x_7, 0);
x_219 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_142);
x_220 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_220, 0, x_142);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Array_append___rarg(x_209, x_218);
lean_inc(x_142);
x_222 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_222, 0, x_142);
lean_ctor_set(x_222, 1, x_211);
lean_ctor_set(x_222, 2, x_221);
x_223 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_142);
x_224 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_224, 0, x_142);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Array_mkArray3___rarg(x_220, x_222, x_224);
x_226 = l_Array_append___rarg(x_209, x_225);
lean_dec(x_225);
lean_inc(x_142);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_142);
lean_ctor_set(x_227, 1, x_211);
lean_ctor_set(x_227, 2, x_226);
x_228 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_229 = l_Lean_Syntax_node5(x_142, x_228, x_207, x_5, x_212, x_214, x_227);
x_230 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_229, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_203);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_ctor_get(x_4, 0);
x_232 = l_Lean_SourceInfo_fromRef(x_231, x_204);
x_233 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Array_mkArray1___rarg(x_234);
x_236 = l_Array_append___rarg(x_209, x_235);
lean_dec(x_235);
lean_inc(x_142);
x_237 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_237, 0, x_142);
lean_ctor_set(x_237, 1, x_211);
lean_ctor_set(x_237, 2, x_236);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_238 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_142);
x_239 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_239, 0, x_142);
lean_ctor_set(x_239, 1, x_211);
lean_ctor_set(x_239, 2, x_238);
x_240 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_241 = l_Lean_Syntax_node5(x_142, x_240, x_207, x_5, x_212, x_237, x_239);
x_242 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_241, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_203);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_243 = lean_ctor_get(x_7, 0);
x_244 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_142);
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_142);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_Array_append___rarg(x_209, x_243);
lean_inc(x_142);
x_247 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_247, 0, x_142);
lean_ctor_set(x_247, 1, x_211);
lean_ctor_set(x_247, 2, x_246);
x_248 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_142);
x_249 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_249, 0, x_142);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_Array_mkArray3___rarg(x_245, x_247, x_249);
x_251 = l_Array_append___rarg(x_209, x_250);
lean_dec(x_250);
lean_inc(x_142);
x_252 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_252, 0, x_142);
lean_ctor_set(x_252, 1, x_211);
lean_ctor_set(x_252, 2, x_251);
x_253 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_254 = l_Lean_Syntax_node5(x_142, x_253, x_207, x_5, x_212, x_237, x_252);
x_255 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_2, x_254, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_203);
return x_255;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpArgs", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_18);
x_21 = l_Lean_Syntax_matchesNull(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_25 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_16);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = l_Lean_Syntax_getArg(x_24, x_20);
lean_dec(x_24);
x_29 = l_Lean_Syntax_getArgs(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(x_2, x_3, x_4, x_7, x_5, x_31, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_18);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(x_2, x_3, x_4, x_7, x_5, x_34, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAllTraceArgsRest", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
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
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
x_21 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4;
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_15, x_24);
x_26 = l_Lean_Syntax_getArg(x_15, x_14);
x_27 = l_Lean_Syntax_isNone(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_inc(x_26);
x_28 = l_Lean_Syntax_matchesNull(x_26, x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lean_Syntax_getArg(x_26, x_19);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(x_15, x_25, x_2, x_4, x_20, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_15);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
x_34 = lean_box(0);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(x_15, x_25, x_2, x_4, x_20, x_35, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_25);
lean_dec(x_15);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpAllTrace", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_14 = l_Lean_Elab_Tactic_withMainContext___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_18);
x_20 = l_Lean_Syntax_matchesNull(x_18, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
x_21 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_22 = l_Lean_Elab_Tactic_withMainContext___rarg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Syntax_getArg(x_18, x_15);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___boxed), 13, 4);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_16);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l_Lean_Elab_Tactic_withMainContext___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___boxed), 13, 4);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_16);
lean_closure_set(x_31, 2, x_30);
lean_closure_set(x_31, 3, x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_Tactic_withMainContext___rarg(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalSimpAllTrace", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4;
x_3 = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(42u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(58u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__2;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(42u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(42u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(51u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_17 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__8;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Meta_dsimpGoal(x_15, x_1, x_2, x_4, x_3, x_17, x_9, x_10, x_11, x_12, x_16);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_22);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_19, 1);
x_36 = lean_ctor_get(x_19, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
lean_dec(x_20);
x_38 = lean_box(0);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_19, 0, x_37);
x_39 = l_Lean_Elab_Tactic_replaceMainGoal(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_35);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_35);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_dec(x_19);
x_49 = lean_ctor_get(x_20, 0);
lean_inc(x_49);
lean_dec(x_20);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_Tactic_replaceMainGoal(x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_48);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_18;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_14);
if (x_64 == 0)
{
return x_14;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_14, 0);
x_66 = lean_ctor_get(x_14, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_14);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_dsimpLocation_x27_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_x27_go(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_19 = l_Lean_Elab_Tactic_dsimpLocation_x27_go(x_1, x_2, x_16, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_17 = l_Lean_Elab_Tactic_dsimpLocation_x27_go(x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1___boxed), 11, 2);
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
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2___boxed), 13, 4);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_17);
x_19 = l_Lean_Elab_Tactic_withMainContext___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = 0;
x_14 = 2;
x_15 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1;
x_16 = lean_box(x_13);
x_17 = lean_box(x_14);
x_18 = lean_box(x_13);
lean_inc(x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Elab_Tactic_withMainContext___rarg(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2;
x_25 = x_60;
goto block_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = l_Lean_Elab_Tactic_expandLocation(x_61);
x_25 = x_62;
goto block_59;
}
block_59:
{
lean_object* x_26; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_23, x_24, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Elab_Tactic_mkSimpCallStx(x_3, x_29, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_10, 5);
lean_inc(x_33);
x_34 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
x_39 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_40 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_37, x_38, x_39, x_36, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_dec(x_27);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_27);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_51 = !lean_is_exclusive(x_30);
if (x_51 == 0)
{
return x_30;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_26);
if (x_55 == 0)
{
return x_26;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_26, 0);
x_57 = lean_ctor_get(x_26, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_26);
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
uint8_t x_63; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimp", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpAutoUnfold", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimp!", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_getOptional_x3f(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_236; 
x_236 = lean_box(0);
x_20 = x_236;
goto block_235;
}
else
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_19);
if (x_237 == 0)
{
x_20 = x_19;
goto block_235;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_19, 0);
lean_inc(x_238);
lean_dec(x_19);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_20 = x_239;
goto block_235;
}
}
block_235:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_14, 5);
lean_inc(x_21);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_15, x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = 1;
x_29 = l_Lean_SourceInfo_fromRef(x_2, x_28);
x_30 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1;
lean_ctor_set_tag(x_24, 2);
lean_ctor_set(x_24, 1, x_30);
lean_ctor_set(x_24, 0, x_29);
x_31 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
x_32 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_23);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_32);
if (lean_obj_tag(x_5) == 0)
{
x_34 = x_32;
goto block_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_5, 0);
x_73 = l_Lean_SourceInfo_fromRef(x_72, x_28);
x_74 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Array_mkArray1___rarg(x_75);
x_34 = x_76;
goto block_71;
}
block_71:
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Array_append___rarg(x_32, x_34);
lean_dec(x_34);
lean_inc(x_23);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_35);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_23);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_37);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
lean_inc(x_38);
x_40 = l_Lean_Syntax_node6(x_23, x_39, x_24, x_4, x_33, x_36, x_38, x_38);
x_41 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
x_43 = lean_array_push(x_32, x_42);
x_44 = l_Array_append___rarg(x_32, x_43);
lean_dec(x_43);
lean_inc(x_23);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_31);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_47 = l_Lean_Syntax_node6(x_23, x_46, x_24, x_4, x_33, x_36, x_38, x_45);
x_48 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_20);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_23);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_23);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_append___rarg(x_32, x_49);
lean_inc(x_23);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_31);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_23);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_23);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_mkArray3___rarg(x_51, x_53, x_55);
x_57 = l_Array_append___rarg(x_32, x_56);
lean_dec(x_56);
lean_inc(x_23);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_23);
lean_ctor_set(x_58, 1, x_31);
lean_ctor_set(x_58, 2, x_57);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_23);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_23);
lean_ctor_set(x_60, 1, x_31);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_62 = l_Lean_Syntax_node6(x_23, x_61, x_24, x_4, x_33, x_36, x_58, x_60);
x_63 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_20, 0);
lean_inc(x_64);
x_65 = lean_array_push(x_32, x_64);
x_66 = l_Array_append___rarg(x_32, x_65);
lean_dec(x_65);
lean_inc(x_23);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_23);
lean_ctor_set(x_67, 1, x_31);
lean_ctor_set(x_67, 2, x_66);
x_68 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_69 = l_Lean_Syntax_node6(x_23, x_68, x_24, x_4, x_33, x_36, x_58, x_67);
x_70 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_69, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_20);
return x_70;
}
}
}
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_24, 1);
lean_inc(x_77);
lean_dec(x_24);
x_78 = 1;
x_79 = l_Lean_SourceInfo_fromRef(x_2, x_78);
x_80 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1;
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
x_83 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_23);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_23);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_83);
if (lean_obj_tag(x_5) == 0)
{
x_85 = x_83;
goto block_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_5, 0);
x_124 = l_Lean_SourceInfo_fromRef(x_123, x_78);
x_125 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_126 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Array_mkArray1___rarg(x_126);
x_85 = x_127;
goto block_122;
}
block_122:
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Array_append___rarg(x_83, x_85);
lean_dec(x_85);
lean_inc(x_23);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_23);
lean_ctor_set(x_87, 1, x_82);
lean_ctor_set(x_87, 2, x_86);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_23);
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_23);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_88);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
lean_inc(x_89);
x_91 = l_Lean_Syntax_node6(x_23, x_90, x_81, x_4, x_84, x_87, x_89, x_89);
x_92 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_91, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_20, 0);
lean_inc(x_93);
x_94 = lean_array_push(x_83, x_93);
x_95 = l_Array_append___rarg(x_83, x_94);
lean_dec(x_94);
lean_inc(x_23);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_23);
lean_ctor_set(x_96, 1, x_82);
lean_ctor_set(x_96, 2, x_95);
x_97 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_98 = l_Lean_Syntax_node6(x_23, x_97, x_81, x_4, x_84, x_87, x_89, x_96);
x_99 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_98, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
lean_dec(x_20);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_7, 0);
x_101 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_23);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_23);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Array_append___rarg(x_83, x_100);
lean_inc(x_23);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_23);
lean_ctor_set(x_104, 1, x_82);
lean_ctor_set(x_104, 2, x_103);
x_105 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_23);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_23);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Array_mkArray3___rarg(x_102, x_104, x_106);
x_108 = l_Array_append___rarg(x_83, x_107);
lean_dec(x_107);
lean_inc(x_23);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_23);
lean_ctor_set(x_109, 1, x_82);
lean_ctor_set(x_109, 2, x_108);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_23);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_23);
lean_ctor_set(x_111, 1, x_82);
lean_ctor_set(x_111, 2, x_110);
x_112 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_113 = l_Lean_Syntax_node6(x_23, x_112, x_81, x_4, x_84, x_87, x_109, x_111);
x_114 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_113, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_20, 0);
lean_inc(x_115);
x_116 = lean_array_push(x_83, x_115);
x_117 = l_Array_append___rarg(x_83, x_116);
lean_dec(x_116);
lean_inc(x_23);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_23);
lean_ctor_set(x_118, 1, x_82);
lean_ctor_set(x_118, 2, x_117);
x_119 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_120 = l_Lean_Syntax_node6(x_23, x_119, x_81, x_4, x_84, x_87, x_109, x_118);
x_121 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_120, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
lean_dec(x_20);
return x_121;
}
}
}
}
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_14, 5);
lean_inc(x_128);
x_129 = 0;
x_130 = l_Lean_SourceInfo_fromRef(x_128, x_129);
lean_dec(x_128);
x_131 = lean_st_ref_get(x_15, x_16);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_133 = lean_ctor_get(x_131, 1);
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
x_135 = 1;
x_136 = l_Lean_SourceInfo_fromRef(x_2, x_135);
x_137 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5;
lean_ctor_set_tag(x_131, 2);
lean_ctor_set(x_131, 1, x_137);
lean_ctor_set(x_131, 0, x_136);
x_138 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
x_139 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_130);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_130);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_139);
if (lean_obj_tag(x_5) == 0)
{
x_141 = x_139;
goto block_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_5, 0);
x_180 = l_Lean_SourceInfo_fromRef(x_179, x_135);
x_181 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Array_mkArray1___rarg(x_182);
x_141 = x_183;
goto block_178;
}
block_178:
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Array_append___rarg(x_139, x_141);
lean_dec(x_141);
lean_inc(x_130);
x_143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_143, 0, x_130);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_142);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_130);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_130);
lean_ctor_set(x_145, 1, x_138);
lean_ctor_set(x_145, 2, x_144);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
lean_inc(x_145);
x_147 = l_Lean_Syntax_node6(x_130, x_146, x_131, x_4, x_140, x_143, x_145, x_145);
x_148 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_147, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_133);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_20, 0);
lean_inc(x_149);
x_150 = lean_array_push(x_139, x_149);
x_151 = l_Array_append___rarg(x_139, x_150);
lean_dec(x_150);
lean_inc(x_130);
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_130);
lean_ctor_set(x_152, 1, x_138);
lean_ctor_set(x_152, 2, x_151);
x_153 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_154 = l_Lean_Syntax_node6(x_130, x_153, x_131, x_4, x_140, x_143, x_145, x_152);
x_155 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_154, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_133);
lean_dec(x_20);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_156 = lean_ctor_get(x_7, 0);
x_157 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_130);
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_130);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Array_append___rarg(x_139, x_156);
lean_inc(x_130);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_130);
lean_ctor_set(x_160, 1, x_138);
lean_ctor_set(x_160, 2, x_159);
x_161 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_130);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_130);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Array_mkArray3___rarg(x_158, x_160, x_162);
x_164 = l_Array_append___rarg(x_139, x_163);
lean_dec(x_163);
lean_inc(x_130);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_130);
lean_ctor_set(x_165, 1, x_138);
lean_ctor_set(x_165, 2, x_164);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_130);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_130);
lean_ctor_set(x_167, 1, x_138);
lean_ctor_set(x_167, 2, x_166);
x_168 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_169 = l_Lean_Syntax_node6(x_130, x_168, x_131, x_4, x_140, x_143, x_165, x_167);
x_170 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_169, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_133);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_171 = lean_ctor_get(x_20, 0);
lean_inc(x_171);
x_172 = lean_array_push(x_139, x_171);
x_173 = l_Array_append___rarg(x_139, x_172);
lean_dec(x_172);
lean_inc(x_130);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_130);
lean_ctor_set(x_174, 1, x_138);
lean_ctor_set(x_174, 2, x_173);
x_175 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_176 = l_Lean_Syntax_node6(x_130, x_175, x_131, x_4, x_140, x_143, x_165, x_174);
x_177 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_176, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_133);
lean_dec(x_20);
return x_177;
}
}
}
}
else
{
lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_184 = lean_ctor_get(x_131, 1);
lean_inc(x_184);
lean_dec(x_131);
x_185 = 1;
x_186 = l_Lean_SourceInfo_fromRef(x_2, x_185);
x_187 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5;
x_188 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
x_190 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_130);
x_191 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_191, 0, x_130);
lean_ctor_set(x_191, 1, x_189);
lean_ctor_set(x_191, 2, x_190);
if (lean_obj_tag(x_5) == 0)
{
x_192 = x_190;
goto block_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_ctor_get(x_5, 0);
x_231 = l_Lean_SourceInfo_fromRef(x_230, x_185);
x_232 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12;
x_233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = l_Array_mkArray1___rarg(x_233);
x_192 = x_234;
goto block_229;
}
block_229:
{
lean_object* x_193; lean_object* x_194; 
x_193 = l_Array_append___rarg(x_190, x_192);
lean_dec(x_192);
lean_inc(x_130);
x_194 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_194, 0, x_130);
lean_ctor_set(x_194, 1, x_189);
lean_ctor_set(x_194, 2, x_193);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_130);
x_196 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_196, 0, x_130);
lean_ctor_set(x_196, 1, x_189);
lean_ctor_set(x_196, 2, x_195);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
lean_inc(x_196);
x_198 = l_Lean_Syntax_node6(x_130, x_197, x_188, x_4, x_191, x_194, x_196, x_196);
x_199 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_198, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_200 = lean_ctor_get(x_20, 0);
lean_inc(x_200);
x_201 = lean_array_push(x_190, x_200);
x_202 = l_Array_append___rarg(x_190, x_201);
lean_dec(x_201);
lean_inc(x_130);
x_203 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_203, 0, x_130);
lean_ctor_set(x_203, 1, x_189);
lean_ctor_set(x_203, 2, x_202);
x_204 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_205 = l_Lean_Syntax_node6(x_130, x_204, x_188, x_4, x_191, x_194, x_196, x_203);
x_206 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_205, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
lean_dec(x_20);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_207 = lean_ctor_get(x_7, 0);
x_208 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_130);
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_130);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Array_append___rarg(x_190, x_207);
lean_inc(x_130);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_130);
lean_ctor_set(x_211, 1, x_189);
lean_ctor_set(x_211, 2, x_210);
x_212 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
lean_inc(x_130);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_130);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Array_mkArray3___rarg(x_209, x_211, x_213);
x_215 = l_Array_append___rarg(x_190, x_214);
lean_dec(x_214);
lean_inc(x_130);
x_216 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_216, 0, x_130);
lean_ctor_set(x_216, 1, x_189);
lean_ctor_set(x_216, 2, x_215);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_130);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_130);
lean_ctor_set(x_218, 1, x_189);
lean_ctor_set(x_218, 2, x_217);
x_219 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_220 = l_Lean_Syntax_node6(x_130, x_219, x_188, x_4, x_191, x_194, x_216, x_218);
x_221 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_220, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_20, 0);
lean_inc(x_222);
x_223 = lean_array_push(x_190, x_222);
x_224 = l_Array_append___rarg(x_190, x_223);
lean_dec(x_223);
lean_inc(x_130);
x_225 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_225, 0, x_130);
lean_ctor_set(x_225, 1, x_189);
lean_ctor_set(x_225, 2, x_224);
x_226 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_227 = l_Lean_Syntax_node6(x_130, x_226, x_188, x_4, x_191, x_194, x_216, x_225);
x_228 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_2, x_20, x_227, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
lean_dec(x_20);
return x_228;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Syntax_isNone(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(1u);
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
lean_dec(x_4);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_17, x_22);
lean_dec(x_17);
x_24 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2;
lean_inc(x_23);
x_25 = l_Lean_Syntax_isOfKind(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_15);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Syntax_getArg(x_23, x_19);
lean_dec(x_23);
x_28 = l_Lean_Syntax_getArgs(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2(x_1, x_2, x_3, x_4, x_6, x_30, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_17);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2(x_1, x_2, x_3, x_4, x_6, x_33, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpTraceArgsRest", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
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
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
x_21 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4;
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_15, x_24);
x_26 = l_Lean_Syntax_isNone(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc(x_25);
x_27 = l_Lean_Syntax_matchesNull(x_25, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg(x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Syntax_getArg(x_25, x_19);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(x_15, x_2, x_4, x_20, x_31, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_30);
lean_dec(x_15);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(x_15, x_2, x_4, x_20, x_34, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_15);
return x_35;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dsimpTrace", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
lean_inc(x_1);
x_12 = l_Lean_Syntax_isOfKind(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_14 = l_Lean_Elab_Tactic_withMainContext___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_inc(x_18);
x_20 = l_Lean_Syntax_matchesNull(x_18, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
x_21 = l_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_22 = l_Lean_Elab_Tactic_withMainContext___rarg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Lean_Syntax_getArg(x_18, x_15);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___boxed), 13, 4);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_16);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_24);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = l_Lean_Elab_Tactic_withMainContext___rarg(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___boxed), 13, 4);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_16);
lean_closure_set(x_31, 2, x_30);
lean_closure_set(x_31, 3, x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withSimpDiagnostics), 10, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_Tactic_withMainContext___rarg(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalDSimpTrace", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4;
x_3 = l_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(82u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(95u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(29u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(82u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(82u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(33u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(47u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__7;
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
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalSimpTrace___spec__1___rarg___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__6 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__6);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__12);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__13 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__13);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__14);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__15 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__15);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__3);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___closed__4);
l_Lean_Elab_Tactic_evalSimpTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__3);
l_Lean_Elab_Tactic_evalSimpTrace___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__3);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__6 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__6);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__7 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__7);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__8 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__8);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__1);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1);
l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__2);
l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1);
l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1);
l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2);
l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__3 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__3);
l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4);
l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5);
l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__1);
l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__2);
l_Lean_Elab_Tactic_evalDSimpTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___closed__1);
l_Lean_Elab_Tactic_evalDSimpTrace___closed__2 = _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalDSimpTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
