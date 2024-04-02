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
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__6;
lean_object* l_Lean_Meta_getSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_dsimpGoal(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___boxed(lean_object**);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__2;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__3;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__1;
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1;
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__6;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__2;
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__3;
lean_object* l_Lean_Meta_instBEqOrigin___boxed(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__6;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace(lean_object*);
lean_object* l_Array_mkArray3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_object* l_Lean_Elab_Tactic_mkSimpContext(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__3;
lean_object* l_Array_mkArray1___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__2;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__3;
lean_object* l_Lean_Meta_instHashableOrigin___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4___closed__2;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Meta_simpAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__1;
lean_object* l_Lean_Elab_Tactic_mkSimpOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__7;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
static lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_mkSimpCallStx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Syntax_unsetTrailing(x_1);
x_9 = l_Lean_Elab_Tactic_mkSimpOnly(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
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
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
x_1 = lean_mk_string_from_bytes("tactic", 6);
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
x_1 = lean_mk_string_from_bytes("Try this: ", 10);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_Elab_Tactic_mkSimpCallStx(x_3, x_24, x_8, x_9, x_10, x_11, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_10, 5);
lean_inc(x_29);
x_30 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_35 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_36 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_2, x_33, x_34, x_35, x_32, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_9);
lean_dec(x_8);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
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
lean_dec(x_11);
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
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
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
x_1 = lean_mk_string_from_bytes("null", 4);
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
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("only", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
x_18 = 0;
x_19 = l_Lean_SourceInfo_fromRef(x_17, x_18);
x_20 = lean_st_ref_get(x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = l_Lean_SourceInfo_fromRef(x_1, x_22);
x_24 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__4;
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_81; 
x_81 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_26 = x_81;
goto block_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_7, 0);
lean_inc(x_82);
lean_dec(x_7);
x_83 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_84 = lean_array_push(x_83, x_82);
x_26 = x_84;
goto block_80;
}
block_80:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_28 = l_Array_append___rarg(x_27, x_26);
x_29 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_19);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
if (lean_obj_tag(x_6) == 0)
{
x_31 = x_27;
goto block_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_6, 0);
lean_inc(x_78);
lean_dec(x_6);
x_79 = lean_array_push(x_27, x_78);
x_31 = x_79;
goto block_77;
}
block_77:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Array_append___rarg(x_27, x_31);
lean_inc(x_19);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
if (lean_obj_tag(x_5) == 0)
{
x_34 = x_27;
goto block_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_5, 0);
lean_inc(x_72);
lean_dec(x_5);
x_73 = l_Lean_SourceInfo_fromRef(x_72, x_22);
x_74 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
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
x_35 = l_Array_append___rarg(x_27, x_34);
lean_inc(x_19);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_35);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_19);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_19);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_37);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
lean_inc(x_38);
x_40 = l_Lean_Syntax_node6(x_19, x_39, x_25, x_30, x_33, x_36, x_38, x_38);
x_41 = lean_apply_10(x_4, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
lean_dec(x_3);
x_43 = lean_array_push(x_27, x_42);
x_44 = l_Array_append___rarg(x_27, x_43);
lean_inc(x_19);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_47 = l_Lean_Syntax_node6(x_19, x_46, x_25, x_30, x_33, x_36, x_38, x_45);
x_48 = lean_apply_10(x_4, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_19);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_append___rarg(x_27, x_49);
lean_inc(x_19);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_19);
lean_ctor_set(x_53, 1, x_29);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_19);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_19);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_mkArray3___rarg(x_51, x_53, x_55);
x_57 = l_Array_append___rarg(x_27, x_56);
lean_inc(x_19);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_19);
lean_ctor_set(x_58, 1, x_29);
lean_ctor_set(x_58, 2, x_57);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_19);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_29);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_62 = l_Lean_Syntax_node6(x_19, x_61, x_25, x_30, x_33, x_36, x_58, x_60);
x_63 = lean_apply_10(x_4, x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_3, 0);
lean_inc(x_64);
lean_dec(x_3);
x_65 = lean_array_push(x_27, x_64);
x_66 = l_Array_append___rarg(x_27, x_65);
lean_inc(x_19);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_29);
lean_ctor_set(x_67, 2, x_66);
x_68 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__5;
x_69 = l_Lean_Syntax_node6(x_19, x_68, x_25, x_30, x_33, x_36, x_58, x_67);
x_70 = lean_apply_10(x_4, x_69, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_70;
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
x_1 = lean_mk_string_from_bytes("simpAutoUnfold", 14);
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
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp!", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_14, 5);
lean_inc(x_17);
x_18 = 0;
x_19 = l_Lean_SourceInfo_fromRef(x_17, x_18);
x_20 = lean_st_ref_get(x_15, x_16);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = l_Lean_SourceInfo_fromRef(x_1, x_22);
x_24 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__3;
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_81; 
x_81 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_26 = x_81;
goto block_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_7, 0);
lean_inc(x_82);
lean_dec(x_7);
x_83 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_84 = lean_array_push(x_83, x_82);
x_26 = x_84;
goto block_80;
}
block_80:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_28 = l_Array_append___rarg(x_27, x_26);
x_29 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_19);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
if (lean_obj_tag(x_6) == 0)
{
x_31 = x_27;
goto block_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_6, 0);
lean_inc(x_78);
lean_dec(x_6);
x_79 = lean_array_push(x_27, x_78);
x_31 = x_79;
goto block_77;
}
block_77:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Array_append___rarg(x_27, x_31);
lean_inc(x_19);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_32);
if (lean_obj_tag(x_5) == 0)
{
x_34 = x_27;
goto block_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_5, 0);
lean_inc(x_72);
lean_dec(x_5);
x_73 = l_Lean_SourceInfo_fromRef(x_72, x_22);
x_74 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
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
x_35 = l_Array_append___rarg(x_27, x_34);
lean_inc(x_19);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_35);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_19);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_19);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_37);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2;
lean_inc(x_38);
x_40 = l_Lean_Syntax_node6(x_19, x_39, x_25, x_30, x_33, x_36, x_38, x_38);
x_41 = lean_apply_10(x_4, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
lean_dec(x_3);
x_43 = lean_array_push(x_27, x_42);
x_44 = l_Array_append___rarg(x_27, x_43);
lean_inc(x_19);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_29);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2;
x_47 = l_Lean_Syntax_node6(x_19, x_46, x_25, x_30, x_33, x_36, x_38, x_45);
x_48 = lean_apply_10(x_4, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_2, 0);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_19);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_append___rarg(x_27, x_49);
lean_inc(x_19);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_19);
lean_ctor_set(x_53, 1, x_29);
lean_ctor_set(x_53, 2, x_52);
x_54 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_19);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_19);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_mkArray3___rarg(x_51, x_53, x_55);
x_57 = l_Array_append___rarg(x_27, x_56);
lean_inc(x_19);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_19);
lean_ctor_set(x_58, 1, x_29);
lean_ctor_set(x_58, 2, x_57);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_19);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_29);
lean_ctor_set(x_60, 2, x_59);
x_61 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2;
x_62 = l_Lean_Syntax_node6(x_19, x_61, x_25, x_30, x_33, x_36, x_58, x_60);
x_63 = lean_apply_10(x_4, x_62, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_3, 0);
lean_inc(x_64);
lean_dec(x_3);
x_65 = lean_array_push(x_27, x_64);
x_66 = l_Array_append___rarg(x_27, x_65);
lean_inc(x_19);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_19);
lean_ctor_set(x_67, 1, x_29);
lean_ctor_set(x_67, 2, x_66);
x_68 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2;
x_69 = l_Lean_Syntax_node6(x_19, x_68, x_25, x_30, x_33, x_36, x_58, x_67);
x_70 = lean_apply_10(x_4, x_69, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
return x_70;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_20 = l_Lean_Syntax_getOptional_x3f(x_19);
lean_dec(x_19);
x_21 = l_Lean_Syntax_getOptional_x3f(x_2);
x_22 = l_Lean_Syntax_getOptional_x3f(x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_42; 
x_42 = lean_box(0);
x_23 = x_42;
goto block_41;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
x_23 = x_20;
goto block_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_23 = x_45;
goto block_41;
}
}
block_41:
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_4);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lambda__2), 12, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_25 = x_37;
goto block_36;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
x_25 = x_21;
goto block_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_25 = x_40;
goto block_36;
}
}
block_36:
{
lean_object* x_26; 
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_32; 
x_32 = lean_box(0);
x_26 = x_32;
goto block_31;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
x_26 = x_22;
goto block_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_26 = x_35;
goto block_31;
}
}
block_31:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lambda__3), 16, 7);
lean_closure_set(x_27, 0, x_4);
lean_closure_set(x_27, 1, x_8);
lean_closure_set(x_27, 2, x_23);
lean_closure_set(x_27, 3, x_24);
lean_closure_set(x_27, 4, x_6);
lean_closure_set(x_27, 5, x_25);
lean_closure_set(x_27, 6, x_26);
x_28 = l_Lean_Elab_Tactic_withMainContext___rarg(x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace___lambda__4), 16, 7);
lean_closure_set(x_29, 0, x_4);
lean_closure_set(x_29, 1, x_8);
lean_closure_set(x_29, 2, x_23);
lean_closure_set(x_29, 3, x_24);
lean_closure_set(x_29, 4, x_6);
lean_closure_set(x_29, 5, x_25);
lean_closure_set(x_29, 6, x_26);
x_30 = l_Lean_Elab_Tactic_withMainContext___rarg(x_29, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_30;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpArgs", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_6);
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
lean_dec(x_7);
lean_dec(x_4);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_18, x_23);
lean_dec(x_18);
x_25 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__2;
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
lean_dec(x_7);
lean_dec(x_4);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_16);
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
x_32 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(x_1, x_2, x_3, x_4, x_5, x_7, x_31, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
x_35 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(x_1, x_2, x_3, x_4, x_5, x_7, x_34, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpTraceArgsRest", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__2;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__2;
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
lean_dec(x_4);
lean_dec(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_15, x_21);
x_23 = l_Lean_Syntax_getArg(x_15, x_14);
x_24 = l_Lean_Syntax_isNone(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_23);
x_25 = l_Lean_Syntax_matchesNull(x_23, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_22);
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
lean_dec(x_4);
lean_dec(x_2);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Syntax_getArg(x_23, x_19);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__6(x_15, x_22, x_20, x_2, x_4, x_29, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_20);
lean_dec(x_22);
lean_dec(x_15);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
x_31 = lean_box(0);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__6(x_15, x_22, x_20, x_2, x_4, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_20);
lean_dec(x_22);
lean_dec(x_15);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpTrace", 9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
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
x_24 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__7(x_1, x_15, x_23, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__7(x_1, x_15, x_26, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__5___boxed(lean_object** _args) {
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
x_18 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalSimpTrace", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__3;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__1() {
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(39u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__4() {
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__5() {
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__5;
x_4 = lean_unsigned_to_nat(45u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Elab_Tactic_mkSimpCallStx(x_1, x_2, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_11, 5);
lean_inc(x_17);
x_18 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_21, 5, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_23 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_24 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_21, x_22, x_23, x_20, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_10);
lean_dec(x_9);
return x_24;
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5() {
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Tactic_getMainGoal(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_23 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Meta_simpAll(x_20, x_18, x_22, x_23, x_7, x_8, x_9, x_10, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Elab_Tactic_replaceMainGoal(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(x_2, x_28, x_1, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_31);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_28);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_ctor_get(x_26, 0);
lean_inc(x_40);
lean_dec(x_26);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_43 = l_Lean_Elab_Tactic_replaceMainGoal(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__1(x_2, x_39, x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_39);
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
}
else
{
uint8_t x_51; 
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
x_51 = !lean_is_exclusive(x_24);
if (x_51 == 0)
{
return x_24;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_24, 0);
x_53 = lean_ctor_get(x_24, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_24);
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
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
return x_19;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_19, 0);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
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
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
return x_15;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_15, 0);
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_15);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpAll", 7);
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
x_1 = lean_mk_string_from_bytes("simp_all", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpAllAutoUnfold", 17);
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
x_1 = lean_mk_string_from_bytes("simp_all!", 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_17 = l_Lean_Syntax_getOptional_x3f(x_1);
lean_dec(x_1);
x_18 = l_Lean_Syntax_getOptional_x3f(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_163; 
x_163 = lean_box(0);
x_19 = x_163;
goto block_162;
}
else
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_17);
if (x_164 == 0)
{
x_19 = x_17;
goto block_162;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_17, 0);
lean_inc(x_165);
lean_dec(x_17);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_19 = x_166;
goto block_162;
}
}
block_162:
{
lean_object* x_20; 
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_158; 
x_158 = lean_box(0);
x_20 = x_158;
goto block_157;
}
else
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_18);
if (x_159 == 0)
{
x_20 = x_18;
goto block_157;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_18, 0);
lean_inc(x_160);
lean_dec(x_18);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_20 = x_161;
goto block_157;
}
}
block_157:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_14, 5);
lean_inc(x_21);
x_22 = 0;
x_23 = l_Lean_SourceInfo_fromRef(x_21, x_22);
x_24 = lean_st_ref_get(x_15, x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 1;
lean_inc(x_3);
x_27 = l_Lean_SourceInfo_fromRef(x_3, x_26);
x_28 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__3;
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_85; 
x_85 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_30 = x_85;
goto block_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
lean_dec(x_20);
x_87 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_88 = lean_array_push(x_87, x_86);
x_30 = x_88;
goto block_84;
}
block_84:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_32 = l_Array_append___rarg(x_31, x_30);
x_33 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_23);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
if (lean_obj_tag(x_19) == 0)
{
x_35 = x_31;
goto block_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_19, 0);
lean_inc(x_82);
lean_dec(x_19);
x_83 = lean_array_push(x_31, x_82);
x_35 = x_83;
goto block_81;
}
block_81:
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Array_append___rarg(x_31, x_35);
lean_inc(x_23);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_23);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_36);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_23);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_38);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
lean_inc(x_39);
x_41 = l_Lean_Syntax_node5(x_23, x_40, x_29, x_34, x_37, x_39, x_39);
x_42 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
lean_dec(x_7);
x_44 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_23);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Array_append___rarg(x_31, x_43);
lean_inc(x_23);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_23);
lean_ctor_set(x_47, 1, x_33);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_23);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_mkArray3___rarg(x_45, x_47, x_49);
x_51 = l_Array_append___rarg(x_31, x_50);
lean_inc(x_23);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_33);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_54 = l_Lean_Syntax_node5(x_23, x_53, x_29, x_34, x_37, x_39, x_52);
x_55 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = l_Lean_SourceInfo_fromRef(x_56, x_26);
x_58 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Array_mkArray1___rarg(x_59);
x_61 = l_Array_append___rarg(x_31, x_60);
lean_inc(x_23);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_23);
lean_ctor_set(x_62, 1, x_33);
lean_ctor_set(x_62, 2, x_61);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_23);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_23);
lean_ctor_set(x_64, 1, x_33);
lean_ctor_set(x_64, 2, x_63);
x_65 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_66 = l_Lean_Syntax_node5(x_23, x_65, x_29, x_34, x_37, x_62, x_64);
x_67 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_66, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_68 = lean_ctor_get(x_7, 0);
lean_inc(x_68);
lean_dec(x_7);
x_69 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_23);
x_70 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_70, 0, x_23);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Array_append___rarg(x_31, x_68);
lean_inc(x_23);
x_72 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_72, 0, x_23);
lean_ctor_set(x_72, 1, x_33);
lean_ctor_set(x_72, 2, x_71);
x_73 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_23);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_23);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Array_mkArray3___rarg(x_70, x_72, x_74);
x_76 = l_Array_append___rarg(x_31, x_75);
lean_inc(x_23);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_23);
lean_ctor_set(x_77, 1, x_33);
lean_ctor_set(x_77, 2, x_76);
x_78 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__2;
x_79 = l_Lean_Syntax_node5(x_23, x_78, x_29, x_34, x_37, x_62, x_77);
x_80 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_79, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
return x_80;
}
}
}
}
}
else
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_4);
x_89 = lean_ctor_get(x_14, 5);
lean_inc(x_89);
x_90 = 0;
x_91 = l_Lean_SourceInfo_fromRef(x_89, x_90);
x_92 = lean_st_ref_get(x_15, x_16);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = 1;
lean_inc(x_3);
x_95 = l_Lean_SourceInfo_fromRef(x_3, x_94);
x_96 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__6;
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_153; 
x_153 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_98 = x_153;
goto block_152;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_20, 0);
lean_inc(x_154);
lean_dec(x_20);
x_155 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_156 = lean_array_push(x_155, x_154);
x_98 = x_156;
goto block_152;
}
block_152:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
x_100 = l_Array_append___rarg(x_99, x_98);
x_101 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
lean_inc(x_91);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_91);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_100);
if (lean_obj_tag(x_19) == 0)
{
x_103 = x_99;
goto block_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_19, 0);
lean_inc(x_150);
lean_dec(x_19);
x_151 = lean_array_push(x_99, x_150);
x_103 = x_151;
goto block_149;
}
block_149:
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Array_append___rarg(x_99, x_103);
lean_inc(x_91);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_91);
lean_ctor_set(x_105, 1, x_101);
lean_ctor_set(x_105, 2, x_104);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_91);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_91);
lean_ctor_set(x_107, 1, x_101);
lean_ctor_set(x_107, 2, x_106);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
lean_inc(x_107);
x_109 = l_Lean_Syntax_node5(x_91, x_108, x_97, x_102, x_105, x_107, x_107);
x_110 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_109, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_93);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_111 = lean_ctor_get(x_7, 0);
lean_inc(x_111);
lean_dec(x_7);
x_112 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_91);
x_113 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_113, 0, x_91);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Array_append___rarg(x_99, x_111);
lean_inc(x_91);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_91);
lean_ctor_set(x_115, 1, x_101);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_91);
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_91);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_mkArray3___rarg(x_113, x_115, x_117);
x_119 = l_Array_append___rarg(x_99, x_118);
lean_inc(x_91);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_91);
lean_ctor_set(x_120, 1, x_101);
lean_ctor_set(x_120, 2, x_119);
x_121 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_122 = l_Lean_Syntax_node5(x_91, x_121, x_97, x_102, x_105, x_107, x_120);
x_123 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_122, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_93);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_5, 0);
lean_inc(x_124);
lean_dec(x_5);
x_125 = l_Lean_SourceInfo_fromRef(x_124, x_94);
x_126 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
x_127 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Array_mkArray1___rarg(x_127);
x_129 = l_Array_append___rarg(x_99, x_128);
lean_inc(x_91);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_91);
lean_ctor_set(x_130, 1, x_101);
lean_ctor_set(x_130, 2, x_129);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_91);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_91);
lean_ctor_set(x_132, 1, x_101);
lean_ctor_set(x_132, 2, x_131);
x_133 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_134 = l_Lean_Syntax_node5(x_91, x_133, x_97, x_102, x_105, x_130, x_132);
x_135 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_134, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_93);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_136 = lean_ctor_get(x_7, 0);
lean_inc(x_136);
lean_dec(x_7);
x_137 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_91);
x_138 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_138, 0, x_91);
lean_ctor_set(x_138, 1, x_137);
x_139 = l_Array_append___rarg(x_99, x_136);
lean_inc(x_91);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_91);
lean_ctor_set(x_140, 1, x_101);
lean_ctor_set(x_140, 2, x_139);
x_141 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_91);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_91);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Array_mkArray3___rarg(x_138, x_140, x_142);
x_144 = l_Array_append___rarg(x_99, x_143);
lean_inc(x_91);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_91);
lean_ctor_set(x_145, 1, x_101);
lean_ctor_set(x_145, 2, x_144);
x_146 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3___closed__5;
x_147 = l_Lean_Syntax_node5(x_91, x_146, x_97, x_102, x_105, x_130, x_145);
x_148 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2(x_3, x_147, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_93);
return x_148;
}
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
x_1 = lean_mk_string_from_bytes("dsimpArgs", 9);
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
lean_dec(x_6);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_16);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_16);
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
x_32 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(x_2, x_3, x_4, x_5, x_7, x_31, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
x_35 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__3(x_2, x_3, x_4, x_5, x_7, x_34, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpAllTraceArgsRest", 20);
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
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_15, x_21);
x_23 = l_Lean_Syntax_getArg(x_15, x_14);
x_24 = l_Lean_Syntax_isNone(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_23);
x_25 = l_Lean_Syntax_matchesNull(x_23, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_22);
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
lean_dec(x_4);
lean_dec(x_2);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_13);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Syntax_getArg(x_23, x_19);
lean_dec(x_23);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(x_15, x_22, x_20, x_2, x_4, x_29, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
x_31 = lean_box(0);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__4(x_15, x_22, x_20, x_2, x_4, x_32, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalSimpAllTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simpAllTrace", 12);
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
x_24 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5(x_1, x_15, x_23, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__5(x_1, x_15, x_26, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
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
return x_14;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalSimpAllTrace", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_3 = l_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(56u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__2;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(41u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__4;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__5;
x_4 = lean_unsigned_to_nat(51u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__7;
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_evalSimpAllTrace___lambda__2___closed__5;
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_ctor_get(x_20, 0);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Tactic_replaceMainGoal(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_34);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_34);
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
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
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
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
return x_14;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_14, 0);
x_53 = lean_ctor_get(x_14, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_14);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
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
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dsimpLocation_x27___lambda__1), 11, 2);
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
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_23, x_24, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_Lean_Elab_Tactic_mkSimpCallStx(x_3, x_27, x_8, x_9, x_10, x_11, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_10, 5);
lean_inc(x_32);
x_33 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_38 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_39 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_2, x_36, x_37, x_38, x_35, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_9);
lean_dec(x_8);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_dec(x_20);
x_45 = lean_ctor_get(x_21, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = l_Lean_Elab_Tactic_expandLocation(x_48);
lean_dec(x_48);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_45, x_46, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_53 = l_Lean_Elab_Tactic_mkSimpCallStx(x_3, x_51, x_8, x_9, x_10, x_11, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_10, 5);
lean_inc(x_56);
x_57 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
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
lean_ctor_set(x_1, 0, x_56);
x_61 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_62 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_2, x_60, x_1, x_61, x_59, x_8, x_9, x_10, x_11, x_55);
lean_dec(x_9);
lean_dec(x_8);
return x_62;
}
else
{
uint8_t x_63; 
lean_free_object(x_1);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_50);
if (x_63 == 0)
{
return x_50;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_50, 0);
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_50);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
lean_dec(x_1);
x_68 = l_Lean_Elab_Tactic_expandLocation(x_67);
lean_dec(x_67);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_69 = l_Lean_Elab_Tactic_dsimpLocation_x27(x_45, x_46, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_72 = l_Lean_Elab_Tactic_mkSimpCallStx(x_3, x_70, x_8, x_9, x_10, x_11, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_10, 5);
lean_inc(x_75);
x_76 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__3;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_75);
x_81 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__2___closed__4;
x_82 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_2, x_79, x_80, x_81, x_78, x_8, x_9, x_10, x_11, x_74);
lean_dec(x_9);
lean_dec(x_8);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_69, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_69, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_85 = x_69;
} else {
 lean_dec_ref(x_69);
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
else
{
uint8_t x_87; 
lean_dec(x_11);
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
x_87 = !lean_is_exclusive(x_20);
if (x_87 == 0)
{
return x_20;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_20, 0);
x_89 = lean_ctor_get(x_20, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_20);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dsimp", 5);
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
x_1 = lean_mk_string_from_bytes("dsimpAutoUnfold", 15);
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
x_1 = lean_mk_string_from_bytes("dsimp!", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Syntax_getOptional_x3f(x_18);
lean_dec(x_18);
x_20 = l_Lean_Syntax_getOptional_x3f(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_151; 
x_151 = lean_box(0);
x_21 = x_151;
goto block_150;
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_19);
if (x_152 == 0)
{
x_21 = x_19;
goto block_150;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_19, 0);
lean_inc(x_153);
lean_dec(x_19);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_21 = x_154;
goto block_150;
}
}
block_150:
{
lean_object* x_22; 
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_146; 
x_146 = lean_box(0);
x_22 = x_146;
goto block_145;
}
else
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_20);
if (x_147 == 0)
{
x_22 = x_20;
goto block_145;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_20, 0);
lean_inc(x_148);
lean_dec(x_20);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_22 = x_149;
goto block_145;
}
}
block_145:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_14, 5);
lean_inc(x_23);
x_24 = 0;
x_25 = l_Lean_SourceInfo_fromRef(x_23, x_24);
x_26 = lean_st_ref_get(x_15, x_16);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 1;
lean_inc(x_3);
x_29 = l_Lean_SourceInfo_fromRef(x_3, x_28);
x_30 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__1;
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
x_33 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
lean_inc(x_25);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
if (lean_obj_tag(x_22) == 0)
{
x_35 = x_33;
goto block_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_22, 0);
lean_inc(x_82);
lean_dec(x_22);
x_83 = lean_array_push(x_33, x_82);
x_35 = x_83;
goto block_81;
}
block_81:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Array_append___rarg(x_33, x_35);
lean_inc(x_25);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_36);
if (lean_obj_tag(x_5) == 0)
{
x_38 = x_33;
goto block_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_5, 0);
lean_inc(x_76);
lean_dec(x_5);
x_77 = l_Lean_SourceInfo_fromRef(x_76, x_28);
x_78 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_mkArray1___rarg(x_79);
x_38 = x_80;
goto block_75;
}
block_75:
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Array_append___rarg(x_33, x_38);
lean_inc(x_25);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_39);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_25);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_25);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_42, 2, x_41);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
lean_inc(x_42);
x_44 = l_Lean_Syntax_node6(x_25, x_43, x_31, x_37, x_34, x_40, x_42, x_42);
x_45 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
x_47 = lean_array_push(x_33, x_46);
x_48 = l_Array_append___rarg(x_33, x_47);
lean_inc(x_25);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_32);
lean_ctor_set(x_49, 2, x_48);
x_50 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_51 = l_Lean_Syntax_node6(x_25, x_50, x_31, x_37, x_34, x_40, x_42, x_49);
x_52 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_51, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_7, 0);
lean_inc(x_53);
lean_dec(x_7);
x_54 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_25);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_25);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_append___rarg(x_33, x_53);
lean_inc(x_25);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_25);
lean_ctor_set(x_57, 1, x_32);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_25);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_25);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Array_mkArray3___rarg(x_55, x_57, x_59);
x_61 = l_Array_append___rarg(x_33, x_60);
lean_inc(x_25);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_25);
lean_ctor_set(x_62, 1, x_32);
lean_ctor_set(x_62, 2, x_61);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_25);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_25);
lean_ctor_set(x_64, 1, x_32);
lean_ctor_set(x_64, 2, x_63);
x_65 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_66 = l_Lean_Syntax_node6(x_25, x_65, x_31, x_37, x_34, x_40, x_62, x_64);
x_67 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_66, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_21, 0);
lean_inc(x_68);
x_69 = lean_array_push(x_33, x_68);
x_70 = l_Array_append___rarg(x_33, x_69);
lean_inc(x_25);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_25);
lean_ctor_set(x_71, 1, x_32);
lean_ctor_set(x_71, 2, x_70);
x_72 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__2;
x_73 = l_Lean_Syntax_node6(x_25, x_72, x_31, x_37, x_34, x_40, x_62, x_71);
x_74 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_73, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
return x_74;
}
}
}
}
}
else
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
x_84 = lean_ctor_get(x_14, 5);
lean_inc(x_84);
x_85 = 0;
x_86 = l_Lean_SourceInfo_fromRef(x_84, x_85);
x_87 = lean_st_ref_get(x_15, x_16);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = 1;
lean_inc(x_3);
x_90 = l_Lean_SourceInfo_fromRef(x_3, x_89);
x_91 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__5;
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__7;
x_94 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__1___closed__1;
lean_inc(x_86);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_86);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_94);
if (lean_obj_tag(x_22) == 0)
{
x_96 = x_94;
goto block_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_22, 0);
lean_inc(x_143);
lean_dec(x_22);
x_144 = lean_array_push(x_94, x_143);
x_96 = x_144;
goto block_142;
}
block_142:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = l_Array_append___rarg(x_94, x_96);
lean_inc(x_86);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_86);
lean_ctor_set(x_98, 1, x_93);
lean_ctor_set(x_98, 2, x_97);
if (lean_obj_tag(x_5) == 0)
{
x_99 = x_94;
goto block_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_ctor_get(x_5, 0);
lean_inc(x_137);
lean_dec(x_5);
x_138 = l_Lean_SourceInfo_fromRef(x_137, x_89);
x_139 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__11;
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Array_mkArray1___rarg(x_140);
x_99 = x_141;
goto block_136;
}
block_136:
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Array_append___rarg(x_94, x_99);
lean_inc(x_86);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_86);
lean_ctor_set(x_101, 1, x_93);
lean_ctor_set(x_101, 2, x_100);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_86);
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_86);
lean_ctor_set(x_103, 1, x_93);
lean_ctor_set(x_103, 2, x_102);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
lean_inc(x_103);
x_105 = l_Lean_Syntax_node6(x_86, x_104, x_92, x_98, x_95, x_101, x_103, x_103);
x_106 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_105, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_88);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_21, 0);
lean_inc(x_107);
x_108 = lean_array_push(x_94, x_107);
x_109 = l_Array_append___rarg(x_94, x_108);
lean_inc(x_86);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_86);
lean_ctor_set(x_110, 1, x_93);
lean_ctor_set(x_110, 2, x_109);
x_111 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_112 = l_Lean_Syntax_node6(x_86, x_111, x_92, x_98, x_95, x_101, x_103, x_110);
x_113 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_112, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_88);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_114 = lean_ctor_get(x_7, 0);
lean_inc(x_114);
lean_dec(x_7);
x_115 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__9;
lean_inc(x_86);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_86);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Array_append___rarg(x_94, x_114);
lean_inc(x_86);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_86);
lean_ctor_set(x_118, 1, x_93);
lean_ctor_set(x_118, 2, x_117);
x_119 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__10;
lean_inc(x_86);
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_86);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Array_mkArray3___rarg(x_116, x_118, x_120);
x_122 = l_Array_append___rarg(x_94, x_121);
lean_inc(x_86);
x_123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_123, 0, x_86);
lean_ctor_set(x_123, 1, x_93);
lean_ctor_set(x_123, 2, x_122);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__8;
lean_inc(x_86);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_86);
lean_ctor_set(x_125, 1, x_93);
lean_ctor_set(x_125, 2, x_124);
x_126 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_127 = l_Lean_Syntax_node6(x_86, x_126, x_92, x_98, x_95, x_101, x_123, x_125);
x_128 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_127, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_88);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_21, 0);
lean_inc(x_129);
x_130 = lean_array_push(x_94, x_129);
x_131 = l_Array_append___rarg(x_94, x_130);
lean_inc(x_86);
x_132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_132, 0, x_86);
lean_ctor_set(x_132, 1, x_93);
lean_ctor_set(x_132, 2, x_131);
x_133 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__2___closed__4;
x_134 = l_Lean_Syntax_node6(x_86, x_133, x_92, x_98, x_95, x_101, x_123, x_132);
x_135 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__1(x_21, x_3, x_134, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_88);
return x_135;
}
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
lean_dec(x_5);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_15);
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_15);
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
x_1 = lean_mk_string_from_bytes("dsimpTraceArgsRest", 18);
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
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
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
lean_dec(x_4);
lean_dec(x_2);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Syntax_getArg(x_15, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_15, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_inc(x_22);
x_24 = l_Lean_Syntax_matchesNull(x_22, x_21);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
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
lean_dec(x_4);
lean_dec(x_2);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Tactic_evalExact___spec__1___rarg(x_13);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_Syntax_getArg(x_22, x_19);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(x_15, x_20, x_2, x_4, x_28, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_22);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__3(x_15, x_20, x_2, x_4, x_31, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalDSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dsimpTrace", 10);
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
x_24 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4(x_1, x_15, x_23, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Tactic_evalDSimpTrace___lambda__4(x_1, x_15, x_26, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("evalDSimpTrace", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1;
x_3 = l_Lean_Elab_Tactic_evalSimpTrace___lambda__3___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalDSimpTrace), 10, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4;
x_3 = l_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(80u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(92u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__1;
x_2 = lean_unsigned_to_nat(29u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(80u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(80u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__4;
x_2 = lean_unsigned_to_nat(33u);
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__5;
x_4 = lean_unsigned_to_nat(47u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__7;
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
l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__3 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__4___closed__3);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__6___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___lambda__7___closed__2);
l_Lean_Elab_Tactic_evalSimpTrace___closed__1 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__1);
l_Lean_Elab_Tactic_evalSimpTrace___closed__2 = _init_l_Lean_Elab_Tactic_evalSimpTrace___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalSimpTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpTrace_declRange(lean_io_mk_world());
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
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllTrace_declRange(lean_io_mk_world());
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
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalDSimpTrace_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
