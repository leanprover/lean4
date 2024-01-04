// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.GuessLex
// Imports: Init Lean.Util.HasConstCache Lean.Meta.CasesOn Lean.Meta.Match.Match Lean.Meta.Tactic.Cleanup Lean.Meta.Tactic.Refl Lean.Elab.Quotation Lean.Elab.RecAppSyntax Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural.Basic Lean.Elab.PreDefinition.WF.TerminationHint Lean.Elab.PreDefinition.WF.PackMutual Lean.Data.Array
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
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__3;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__15;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_generateMeasures___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__9;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__9;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322_(uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_ofNat___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__26;
static lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__10;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_guessLex___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__23;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__5;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__4;
lean_object* lean_name_append_after(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__9;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_buildTermWF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__6;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__21;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_inspectCall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__7;
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_guessLex___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__18;
LEAN_EXPORT lean_object* l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__2;
static lean_object* l_Lean_Elab_WF_GuessLex_generateMeasures___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__8;
static lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__4___boxed(lean_object**);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__4;
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
extern uint8_t l_instInhabitedBool;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__29;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__25;
lean_object* l_Lean_Meta_CasesOnApp_refineThrough_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9_(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___closed__3;
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6;
static lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__20;
static lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__8;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__35;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_SavedLocalContext_run___spec__1(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_create(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__3;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__1;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_Match_Value_0__Lean_Meta_isUIntTypeName___spec__1(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateMeasures(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_create(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__23;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__8;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__21;
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_guessLex___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__5;
static lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__1;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__7;
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Elab_WF_GuessLex_generateMeasures___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__11;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__19;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_WF_guessLex___spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__7;
static lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__3;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__16;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__2;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve___at_Lean_Elab_WF_guessLex___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_guessLex___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__6;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__32;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_formatTable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__22;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___closed__1;
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__3;
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__4;
extern lean_object* l_String_instInhabitedString;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__3;
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_isForbidden___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__4;
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1;
static lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1(lean_object*);
lean_object* l_Lean_Elab_goalsToMessageData(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_runTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__7;
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_Elab_Structural_recArgHasLooseBVarsAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel(uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_mk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__30;
uint8_t l_Lean_Expr_isLit(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__2;
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_formatTable___spec__2(size_t, size_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__6;
static lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__33;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__2;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__27;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__5;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__34;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processApp(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__12;
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__3;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__10;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__10;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__28;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___boxed(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__1;
static lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HasConstCache_containsUnsafe(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__25;
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_SavedLocalContext_run___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__2;
lean_object* l_Lean_log___at_Lean_Meta_computeSynthOrder___spec__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processRec(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__2;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__2;
LEAN_EXPORT uint8_t l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_isForbidden(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__2;
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__2;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_reportUnsolvedGoals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_buildTermWF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__5;
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackMutualArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackMutualArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__1;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__8;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_formatTable___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__12;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6(lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_showInferredTerminationBy;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__2;
LEAN_EXPORT uint8_t l_Lean_Elab_WF_GuessLex_GuessLexRel_ofNat(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__3;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__6;
static lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___closed__1;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion(lean_object*);
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_WF_TerminationWF_unexpand___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__4;
static lean_object* l_Lean_Elab_WF_GuessLex_generateMeasures___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_WF_TerminationWF_unexpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_mkSizeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toCtorIdx(uint8_t);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_instReprGuessLexRel___closed__1;
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__10;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__5;
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__24;
lean_object* lean_string_length(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__17;
static lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__2;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__26;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_create___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__24;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames_freshen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__18;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__31;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4;
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___closed__1;
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel(uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_levelOne;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__15;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_create___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___boxed(lean_object**);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainMutualFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve___at_Lean_Elab_WF_guessLex___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___boxed(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__12;
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_inspectCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_unresolveNameGlobal___at_Lean_Elab_WF_TerminationWF_unexpand___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__5;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__13;
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___lambda__1(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainMutualFailure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_formatTable___boxed(lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__8;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__9;
lean_object* l_Lean_Elab_ensureNoRecFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
static lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__19;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateMeasures___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__3;
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_toCasesOnApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__1;
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___closed__1;
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__11;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_guessLex___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instReprGuessLexRel;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainNonMutualFailure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel(uint8_t);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__1;
LEAN_EXPORT uint8_t l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___closed__6;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_guessLex___spec__12(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__13;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__5;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__9;
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__22;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_inspectCall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__6;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toCtorIdx___boxed(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_guessLex___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Elab_WF_guessLex___lambda__2___closed__2;
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("showInferredTerminationBy", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("In recursive definitions, show the inferred `termination_by` measure.", 69);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_3 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("WF", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("GuessLex", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6;
x_2 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__7;
x_3 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__8;
x_4 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__9;
x_5 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__2;
x_3 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__5;
x_4 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__10;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames_freshen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
lean_inc(x_2);
x_8 = l_Lean_resolveGlobalName___at_Lean_Elab_WF_TerminationWF_unexpand___spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Array_contains___at___private_Lean_Meta_Match_Value_0__Lean_Meta_isUIntTypeName___spec__1(x_1, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_List_isEmpty___rarg(x_10);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_8);
x_14 = l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1;
x_15 = lean_name_append_after(x_2, x_14);
x_2 = x_15;
x_7 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_8);
lean_dec(x_10);
x_17 = l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1;
x_18 = lean_name_append_after(x_2, x_17);
x_2 = x_18;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = l_Array_contains___at___private_Lean_Meta_Match_Value_0__Lean_Meta_isUIntTypeName___spec__1(x_1, x_2);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_List_isEmpty___rarg(x_20);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1;
x_25 = lean_name_append_after(x_2, x_24);
x_2 = x_25;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
x_28 = l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1;
x_29 = lean_name_append_after(x_2, x_28);
x_2 = x_29;
x_7 = x_21;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_GuessLex_naryVarNames_freshen(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_10, x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_9, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_9, x_22);
lean_dec(x_9);
x_24 = lean_array_fget(x_3, x_10);
x_25 = l_Lean_Expr_fvarId_x21(x_24);
lean_inc(x_13);
x_26 = l_Lean_FVarId_getUserName(x_25, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Name_hasMacroScopes(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_15);
x_30 = l_Lean_Elab_WF_GuessLex_naryVarNames_freshen(x_12, x_27, x_13, x_14, x_15, x_16, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_push(x_12, x_31);
x_34 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_23;
x_10 = x_34;
x_11 = lean_box(0);
x_12 = x_33;
x_17 = x_32;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_27);
x_36 = lean_nat_add(x_10, x_22);
x_37 = l_Nat_repr(x_36);
x_38 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___closed__1;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Name_str___override(x_42, x_41);
lean_inc(x_15);
x_44 = l_Lean_Elab_WF_GuessLex_naryVarNames_freshen(x_12, x_43, x_13, x_14, x_15, x_16, x_28);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_push(x_12, x_45);
x_48 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_23;
x_10 = x_48;
x_11 = lean_box(0);
x_12 = x_47;
x_17 = x_46;
goto _start;
}
}
else
{
uint8_t x_50; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_50 = !lean_is_exclusive(x_26);
if (x_50 == 0)
{
return x_26;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_26, 0);
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_26);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_12);
lean_ctor_set(x_54, 1, x_17);
return x_54;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_array_get_size(x_2);
lean_inc(x_1);
x_10 = l_Array_extract___rarg(x_2, x_1, x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
lean_inc(x_11);
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1(x_1, x_2, x_10, x_11, x_14, x_12, x_11, x_13, x_11, x_12, lean_box(0), x_15, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
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
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_st_ref_take(x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_HasConstCache_containsUnsafe(x_1, x_2, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_set(x_4, x_15, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
x_17 = lean_nat_dec_lt(x_14, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1;
lean_inc(x_14);
x_19 = lean_mk_array(x_14, x_18);
x_20 = lean_nat_sub(x_14, x_15);
lean_dec(x_14);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_19, x_20);
x_22 = lean_apply_7(x_3, x_4, x_21, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_take(x_6, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_push(x_26, x_23);
x_29 = lean_st_ref_set(x_6, x_28, x_27);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
return x_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_22, 0);
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_40 = l_Lean_Meta_etaExpand(x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_1, x_2, x_3, x_4, x_41, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
return x_43;
}
else
{
uint8_t x_44; 
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
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processRec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_12, x_1);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_16, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___rarg(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_25);
x_27 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
x_31 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_28, x_30);
x_32 = lean_array_get_size(x_31);
x_33 = l_Lean_Meta_Match_MatcherInfo_arity(x_24);
x_34 = lean_nat_dec_lt(x_32, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = l_List_redLength___rarg(x_12);
x_36 = lean_mk_empty_array_with_capacity(x_35);
lean_dec(x_35);
x_37 = l_List_toArrayAux___rarg(x_12, x_36);
x_38 = lean_ctor_get(x_24, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
x_40 = l_Array_extract___rarg(x_31, x_25, x_39);
x_41 = lean_nat_dec_lt(x_39, x_32);
x_42 = lean_nat_add(x_39, x_29);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_43);
lean_inc(x_44);
lean_inc(x_31);
x_45 = l_Array_toSubarray___rarg(x_31, x_42, x_44);
x_46 = l_Array_ofSubarray___rarg(x_45);
x_47 = lean_ctor_get(x_24, 2);
lean_inc(x_47);
x_48 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_24);
lean_dec(x_24);
x_49 = lean_nat_add(x_44, x_48);
lean_dec(x_48);
lean_inc(x_49);
lean_inc(x_31);
x_50 = l_Array_toSubarray___rarg(x_31, x_44, x_49);
x_51 = l_Array_ofSubarray___rarg(x_50);
lean_inc(x_31);
x_52 = l_Array_toSubarray___rarg(x_31, x_49, x_32);
x_53 = l_Array_ofSubarray___rarg(x_52);
if (x_41 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_39);
lean_dec(x_31);
x_54 = l_Lean_instInhabitedExpr;
x_55 = l___private_Init_Util_0__outOfBounds___rarg(x_54);
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_11);
lean_ctor_set(x_56, 1, x_37);
lean_ctor_set(x_56, 2, x_38);
lean_ctor_set(x_56, 3, x_40);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_46);
lean_ctor_set(x_56, 6, x_47);
lean_ctor_set(x_56, 7, x_51);
lean_ctor_set(x_56, 8, x_53);
lean_ctor_set(x_14, 0, x_56);
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_array_fget(x_31, x_39);
lean_dec(x_39);
lean_dec(x_31);
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_11);
lean_ctor_set(x_58, 1, x_37);
lean_ctor_set(x_58, 2, x_38);
lean_ctor_set(x_58, 3, x_40);
lean_ctor_set(x_58, 4, x_57);
lean_ctor_set(x_58, 5, x_46);
lean_ctor_set(x_58, 6, x_47);
lean_ctor_set(x_58, 7, x_51);
lean_ctor_set(x_58, 8, x_53);
lean_ctor_set(x_14, 0, x_58);
return x_13;
}
}
else
{
lean_object* x_59; 
lean_dec(x_32);
lean_dec(x_31);
lean_free_object(x_14);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
x_59 = lean_box(0);
lean_ctor_set(x_13, 0, x_59);
return x_13;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_60 = lean_ctor_get(x_14, 0);
lean_inc(x_60);
lean_dec(x_14);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_61);
x_63 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1;
lean_inc(x_62);
x_64 = lean_mk_array(x_62, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_sub(x_62, x_65);
lean_dec(x_62);
x_67 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_64, x_66);
x_68 = lean_array_get_size(x_67);
x_69 = l_Lean_Meta_Match_MatcherInfo_arity(x_60);
x_70 = lean_nat_dec_lt(x_68, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_71 = l_List_redLength___rarg(x_12);
x_72 = lean_mk_empty_array_with_capacity(x_71);
lean_dec(x_71);
x_73 = l_List_toArrayAux___rarg(x_12, x_72);
x_74 = lean_ctor_get(x_60, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
x_76 = l_Array_extract___rarg(x_67, x_61, x_75);
x_77 = lean_nat_dec_lt(x_75, x_68);
x_78 = lean_nat_add(x_75, x_65);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
x_80 = lean_nat_add(x_78, x_79);
lean_dec(x_79);
lean_inc(x_80);
lean_inc(x_67);
x_81 = l_Array_toSubarray___rarg(x_67, x_78, x_80);
x_82 = l_Array_ofSubarray___rarg(x_81);
x_83 = lean_ctor_get(x_60, 2);
lean_inc(x_83);
x_84 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_60);
lean_dec(x_60);
x_85 = lean_nat_add(x_80, x_84);
lean_dec(x_84);
lean_inc(x_85);
lean_inc(x_67);
x_86 = l_Array_toSubarray___rarg(x_67, x_80, x_85);
x_87 = l_Array_ofSubarray___rarg(x_86);
lean_inc(x_67);
x_88 = l_Array_toSubarray___rarg(x_67, x_85, x_68);
x_89 = l_Array_ofSubarray___rarg(x_88);
if (x_77 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_75);
lean_dec(x_67);
x_90 = l_Lean_instInhabitedExpr;
x_91 = l___private_Init_Util_0__outOfBounds___rarg(x_90);
x_92 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_92, 0, x_11);
lean_ctor_set(x_92, 1, x_73);
lean_ctor_set(x_92, 2, x_74);
lean_ctor_set(x_92, 3, x_76);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_82);
lean_ctor_set(x_92, 6, x_83);
lean_ctor_set(x_92, 7, x_87);
lean_ctor_set(x_92, 8, x_89);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_13, 0, x_93);
return x_13;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_array_fget(x_67, x_75);
lean_dec(x_75);
lean_dec(x_67);
x_95 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_95, 0, x_11);
lean_ctor_set(x_95, 1, x_73);
lean_ctor_set(x_95, 2, x_74);
lean_ctor_set(x_95, 3, x_76);
lean_ctor_set(x_95, 4, x_94);
lean_ctor_set(x_95, 5, x_82);
lean_ctor_set(x_95, 6, x_83);
lean_ctor_set(x_95, 7, x_87);
lean_ctor_set(x_95, 8, x_89);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_13, 0, x_96);
return x_13;
}
}
else
{
lean_object* x_97; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_60);
lean_dec(x_12);
lean_dec(x_11);
x_97 = lean_box(0);
lean_ctor_set(x_13, 0, x_97);
return x_13;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_98 = lean_ctor_get(x_13, 1);
lean_inc(x_98);
lean_dec(x_13);
x_99 = lean_ctor_get(x_14, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_100 = x_14;
} else {
 lean_dec_ref(x_14);
 x_100 = lean_box(0);
}
x_101 = lean_unsigned_to_nat(0u);
x_102 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_101);
x_103 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1;
lean_inc(x_102);
x_104 = lean_mk_array(x_102, x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_102, x_105);
lean_dec(x_102);
x_107 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_104, x_106);
x_108 = lean_array_get_size(x_107);
x_109 = l_Lean_Meta_Match_MatcherInfo_arity(x_99);
x_110 = lean_nat_dec_lt(x_108, x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = l_List_redLength___rarg(x_12);
x_112 = lean_mk_empty_array_with_capacity(x_111);
lean_dec(x_111);
x_113 = l_List_toArrayAux___rarg(x_12, x_112);
x_114 = lean_ctor_get(x_99, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_99, 0);
lean_inc(x_115);
x_116 = l_Array_extract___rarg(x_107, x_101, x_115);
x_117 = lean_nat_dec_lt(x_115, x_108);
x_118 = lean_nat_add(x_115, x_105);
x_119 = lean_ctor_get(x_99, 1);
lean_inc(x_119);
x_120 = lean_nat_add(x_118, x_119);
lean_dec(x_119);
lean_inc(x_120);
lean_inc(x_107);
x_121 = l_Array_toSubarray___rarg(x_107, x_118, x_120);
x_122 = l_Array_ofSubarray___rarg(x_121);
x_123 = lean_ctor_get(x_99, 2);
lean_inc(x_123);
x_124 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_99);
lean_dec(x_99);
x_125 = lean_nat_add(x_120, x_124);
lean_dec(x_124);
lean_inc(x_125);
lean_inc(x_107);
x_126 = l_Array_toSubarray___rarg(x_107, x_120, x_125);
x_127 = l_Array_ofSubarray___rarg(x_126);
lean_inc(x_107);
x_128 = l_Array_toSubarray___rarg(x_107, x_125, x_108);
x_129 = l_Array_ofSubarray___rarg(x_128);
if (x_117 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_115);
lean_dec(x_107);
x_130 = l_Lean_instInhabitedExpr;
x_131 = l___private_Init_Util_0__outOfBounds___rarg(x_130);
x_132 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_132, 0, x_11);
lean_ctor_set(x_132, 1, x_113);
lean_ctor_set(x_132, 2, x_114);
lean_ctor_set(x_132, 3, x_116);
lean_ctor_set(x_132, 4, x_131);
lean_ctor_set(x_132, 5, x_122);
lean_ctor_set(x_132, 6, x_123);
lean_ctor_set(x_132, 7, x_127);
lean_ctor_set(x_132, 8, x_129);
if (lean_is_scalar(x_100)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_100;
}
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_98);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_array_fget(x_107, x_115);
lean_dec(x_115);
lean_dec(x_107);
x_136 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_136, 0, x_11);
lean_ctor_set(x_136, 1, x_113);
lean_ctor_set(x_136, 2, x_114);
lean_ctor_set(x_136, 3, x_116);
lean_ctor_set(x_136, 4, x_135);
lean_ctor_set(x_136, 5, x_122);
lean_ctor_set(x_136, 6, x_123);
lean_ctor_set(x_136, 7, x_127);
lean_ctor_set(x_136, 8, x_129);
if (lean_is_scalar(x_100)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_100;
}
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_98);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_12);
lean_dec(x_11);
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_98);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_10);
lean_dec(x_2);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_9);
return x_142;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_tag(x_10, 1);
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
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg), 9, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = l_Lean_Expr_beta(x_1, x_2);
x_16 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected `casesOn` application alternative", 44);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nat application", 15);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_eq(x_5, x_16);
lean_dec(x_16);
lean_dec(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_indentExpr(x_1);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_6);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___rarg(x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
x_32 = lean_box(0);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__1(x_1, x_7, x_2, x_3, x_4, x_8, x_32, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_6, x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_17 = lean_array_uget(x_5, x_6);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2), 15, 6);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_20);
lean_closure_set(x_22, 5, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg(x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_8 = x_24;
x_15 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_33; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_15);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___boxed), 15, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_tag(x_10, 1);
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
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___rarg___boxed), 8, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7___rarg), 9, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_7);
x_17 = lean_nat_dec_eq(x_5, x_16);
lean_dec(x_16);
lean_dec(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_indentExpr(x_1);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_indentExpr(x_6);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___rarg(x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
x_32 = lean_box(0);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__1(x_1, x_7, x_2, x_3, x_4, x_8, x_32, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_6, x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_17 = lean_array_uget(x_5, x_6);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg___lambda__1), 15, 6);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_20);
lean_closure_set(x_22, 5, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7___rarg(x_21, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_6, x_26);
x_6 = x_27;
x_8 = x_24;
x_15 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_33; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_15);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg___boxed), 15, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___lambda__1), 9, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_13, x_5, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___lambda__1), 9, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_13, x_5, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___lambda__1), 9, 3);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_13, x_5, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_expr_instantiate1(x_1, x_6);
lean_dec(x_6);
lean_dec(x_1);
x_15 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_dec(x_6);
switch (lean_obj_tag(x_1)) {
case 4:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isConstOf(x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
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
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
case 5:
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_1);
x_18 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1___rarg(x_2, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_21 = l_Lean_Meta_toCasesOnApp_x3f(x_1, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_2, x_3, x_1);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_26);
x_28 = l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
return x_28;
}
else
{
lean_object* x_29; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_26);
x_29 = l_Lean_Meta_CasesOnApp_refineThrough_x3f(x_26, x_5, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_ctor_get(x_29, 1);
x_35 = lean_ctor_get(x_29, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_26, 6);
lean_inc(x_37);
x_38 = lean_ctor_get(x_26, 7);
lean_inc(x_38);
lean_dec(x_26);
x_39 = l_Array_zip___rarg(x_38, x_36);
lean_dec(x_36);
lean_dec(x_38);
x_40 = l_Array_zip___rarg(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
x_41 = lean_array_get_size(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_nat_dec_lt(x_42, x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
lean_ctor_set(x_29, 0, x_44);
return x_29;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_41, x_41);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_box(0);
lean_ctor_set(x_29, 0, x_46);
return x_29;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_29);
x_47 = 0;
x_48 = lean_usize_of_nat(x_41);
lean_dec(x_41);
x_49 = lean_box(0);
x_50 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg(x_2, x_3, x_4, x_1, x_40, x_47, x_48, x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
lean_dec(x_40);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_51 = lean_ctor_get(x_29, 1);
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
lean_dec(x_30);
x_53 = lean_ctor_get(x_26, 6);
lean_inc(x_53);
x_54 = lean_ctor_get(x_26, 7);
lean_inc(x_54);
lean_dec(x_26);
x_55 = l_Array_zip___rarg(x_54, x_52);
lean_dec(x_52);
lean_dec(x_54);
x_56 = l_Array_zip___rarg(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_57 = lean_array_get_size(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_lt(x_58, x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
return x_61;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_57, x_57);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_51);
return x_64;
}
else
{
size_t x_65; size_t x_66; lean_object* x_67; lean_object* x_68; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_67 = lean_box(0);
x_68 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg(x_2, x_3, x_4, x_1, x_56, x_65, x_66, x_67, x_7, x_8, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_56);
return x_68;
}
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_26);
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
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_29);
if (x_69 == 0)
{
return x_29;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_29, 0);
x_71 = lean_ctor_get(x_29, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_29);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
else
{
uint8_t x_73; 
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
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_21);
if (x_73 == 0)
{
return x_21;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_21, 0);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_21);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_18, 1);
lean_inc(x_77);
lean_dec(x_18);
x_78 = lean_ctor_get(x_19, 0);
lean_inc(x_78);
lean_dec(x_19);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_79 = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(x_2, x_3, x_1);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_78);
x_80 = l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
return x_80;
}
else
{
lean_object* x_81; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_78);
x_81 = l_Lean_Meta_MatcherApp_refineThrough_x3f(x_78, x_5, x_9, x_10, x_11, x_12, x_77);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_78);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg(x_2, x_3, x_4, x_5, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_83);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_86 = lean_ctor_get(x_81, 1);
x_87 = lean_ctor_get(x_81, 0);
lean_dec(x_87);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_78, 7);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 6);
lean_inc(x_90);
lean_dec(x_78);
x_91 = l_Array_zip___rarg(x_90, x_88);
lean_dec(x_88);
lean_dec(x_90);
x_92 = l_Array_zip___rarg(x_89, x_91);
lean_dec(x_91);
lean_dec(x_89);
x_93 = lean_array_get_size(x_92);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_dec_lt(x_94, x_93);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_box(0);
lean_ctor_set(x_81, 0, x_96);
return x_81;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_93, x_93);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_box(0);
lean_ctor_set(x_81, 0, x_98);
return x_81;
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; lean_object* x_102; 
lean_free_object(x_81);
x_99 = 0;
x_100 = lean_usize_of_nat(x_93);
lean_dec(x_93);
x_101 = lean_box(0);
x_102 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg(x_2, x_3, x_4, x_1, x_92, x_99, x_100, x_101, x_7, x_8, x_9, x_10, x_11, x_12, x_86);
lean_dec(x_92);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
lean_dec(x_81);
x_104 = lean_ctor_get(x_82, 0);
lean_inc(x_104);
lean_dec(x_82);
x_105 = lean_ctor_get(x_78, 7);
lean_inc(x_105);
x_106 = lean_ctor_get(x_78, 6);
lean_inc(x_106);
lean_dec(x_78);
x_107 = l_Array_zip___rarg(x_106, x_104);
lean_dec(x_104);
lean_dec(x_106);
x_108 = l_Array_zip___rarg(x_105, x_107);
lean_dec(x_107);
lean_dec(x_105);
x_109 = lean_array_get_size(x_108);
x_110 = lean_unsigned_to_nat(0u);
x_111 = lean_nat_dec_lt(x_110, x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_103);
return x_113;
}
else
{
uint8_t x_114; 
x_114 = lean_nat_dec_le(x_109, x_109);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_103);
return x_116;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; 
x_117 = 0;
x_118 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_119 = lean_box(0);
x_120 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg(x_2, x_3, x_4, x_1, x_108, x_117, x_118, x_119, x_7, x_8, x_9, x_10, x_11, x_12, x_103);
lean_dec(x_108);
return x_120;
}
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_78);
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
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_81);
if (x_121 == 0)
{
return x_81;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_81, 0);
x_123 = lean_ctor_get(x_81, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_81);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
case 6:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_1, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_1, 2);
lean_inc(x_127);
x_128 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_126);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_129 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_126, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__1), 13, 5);
lean_closure_set(x_131, 0, x_127);
lean_closure_set(x_131, 1, x_2);
lean_closure_set(x_131, 2, x_3);
lean_closure_set(x_131, 3, x_4);
lean_closure_set(x_131, 4, x_5);
x_132 = 0;
x_133 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg(x_125, x_128, x_126, x_131, x_132, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
return x_133;
}
else
{
uint8_t x_134; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
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
x_134 = !lean_is_exclusive(x_129);
if (x_134 == 0)
{
return x_129;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_129, 0);
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_129);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
case 7:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_1, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 2);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_139);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_142 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_139, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__1), 13, 5);
lean_closure_set(x_144, 0, x_140);
lean_closure_set(x_144, 1, x_2);
lean_closure_set(x_144, 2, x_3);
lean_closure_set(x_144, 3, x_4);
lean_closure_set(x_144, 4, x_5);
x_145 = 0;
x_146 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___rarg(x_138, x_141, x_139, x_144, x_145, x_7, x_8, x_9, x_10, x_11, x_12, x_143);
return x_146;
}
else
{
uint8_t x_147; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
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
x_147 = !lean_is_exclusive(x_142);
if (x_147 == 0)
{
return x_142;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_142, 0);
x_149 = lean_ctor_get(x_142, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_142);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
case 8:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_1, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_1, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_1, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_1, 3);
lean_inc(x_154);
lean_dec(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_152);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_155 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_152, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_153);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_157 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_153, x_7, x_8, x_9, x_10, x_11, x_12, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__1), 13, 5);
lean_closure_set(x_159, 0, x_154);
lean_closure_set(x_159, 1, x_2);
lean_closure_set(x_159, 2, x_3);
lean_closure_set(x_159, 3, x_4);
lean_closure_set(x_159, 4, x_5);
x_160 = 0;
x_161 = l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___rarg(x_151, x_152, x_153, x_159, x_160, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
return x_161;
}
else
{
uint8_t x_162; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
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
x_162 = !lean_is_exclusive(x_157);
if (x_162 == 0)
{
return x_157;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_157, 0);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_157);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
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
x_166 = !lean_is_exclusive(x_155);
if (x_166 == 0)
{
return x_155;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_155, 0);
x_168 = lean_ctor_get(x_155, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_155);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
case 10:
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_1, 1);
lean_inc(x_170);
x_171 = l_Lean_getRecAppSyntax_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_170, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; 
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_11, 5);
lean_inc(x_174);
x_175 = l_Lean_replaceRef(x_173, x_174);
lean_dec(x_174);
lean_dec(x_173);
x_176 = lean_ctor_get(x_11, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_11, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_11, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_11, 3);
lean_inc(x_179);
x_180 = lean_ctor_get(x_11, 4);
lean_inc(x_180);
x_181 = lean_ctor_get(x_11, 6);
lean_inc(x_181);
x_182 = lean_ctor_get(x_11, 7);
lean_inc(x_182);
x_183 = lean_ctor_get(x_11, 8);
lean_inc(x_183);
x_184 = lean_ctor_get(x_11, 9);
lean_inc(x_184);
x_185 = lean_ctor_get(x_11, 10);
lean_inc(x_185);
x_186 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
lean_dec(x_11);
x_187 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_187, 0, x_176);
lean_ctor_set(x_187, 1, x_177);
lean_ctor_set(x_187, 2, x_178);
lean_ctor_set(x_187, 3, x_179);
lean_ctor_set(x_187, 4, x_180);
lean_ctor_set(x_187, 5, x_175);
lean_ctor_set(x_187, 6, x_181);
lean_ctor_set(x_187, 7, x_182);
lean_ctor_set(x_187, 8, x_183);
lean_ctor_set(x_187, 9, x_184);
lean_ctor_set(x_187, 10, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*11, x_186);
x_188 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_170, x_7, x_8, x_9, x_10, x_187, x_12, x_13);
return x_188;
}
}
case 11:
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_1, 2);
lean_inc(x_189);
lean_dec(x_1);
x_190 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_2, x_3, x_4, x_5, x_189, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_190;
}
default: 
{
lean_object* x_191; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_191 = l_Lean_Elab_ensureNoRecFn(x_2, x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_191, 0);
lean_dec(x_193);
x_194 = lean_box(0);
lean_ctor_set(x_191, 0, x_194);
return x_191;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_191);
if (x_198 == 0)
{
return x_191;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_191, 0);
x_200 = lean_ctor_get(x_191, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_5);
x_13 = l_Lean_Elab_WF_GuessLex_withRecApps_containsRecFn___rarg(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
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
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg___lambda__2(x_5, x_1, x_2, x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_6, x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_17 = lean_array_uget(x_5, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_1, x_2, x_3, x_4, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_6 = x_22;
x_8 = x_19;
x_15 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_15);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1___rarg___boxed), 15, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_array_set(x_7, x_8, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_8, x_19);
lean_dec(x_8);
x_6 = x_16;
x_7 = x_18;
x_8 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_8);
x_22 = lean_array_get_size(x_7);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_7);
x_25 = l_Lean_Expr_isConstOf(x_6, x_1);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_5);
x_26 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_6);
x_27 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_22, x_22);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_22);
lean_dec(x_7);
x_29 = l_Lean_Expr_isConstOf(x_6, x_1);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_5);
x_30 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_6);
x_31 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_31;
}
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1___rarg(x_1, x_2, x_3, x_4, x_7, x_32, x_33, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Expr_isConstOf(x_6, x_1);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_5);
x_38 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_36);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_6);
x_39 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_36);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__2___rarg), 15, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_13);
x_15 = l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
lean_inc(x_5);
x_19 = l_Lean_Expr_withAppAux___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_5, x_16, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps_processApp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps_processApp___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_matchMatcherApp_x3f___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwError___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__7(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___rarg(x_1, x_13, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__9(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___rarg(x_1, x_13, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__10(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___rarg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_withLetDecl___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__11(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_processApp___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
return x_18;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___closed__1;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_17 = lean_st_mk_ref(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_18);
x_20 = l_Lean_Elab_WF_GuessLex_withRecApps_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_18, x_14, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_18, x_21);
lean_dec(x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_14, x_24);
lean_dec(x_14);
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
lean_dec(x_18);
lean_dec(x_14);
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wf", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__7;
x_2 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__1;
x_3 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("withRecApps: ", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_11, x_6, x_7, x_8, x_9, x_10);
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
x_17 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1(x_1, x_2, x_5, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
lean_inc(x_4);
x_19 = l_Lean_indentExpr(x_4);
x_20 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__5;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_11, x_23, x_6, x_7, x_8, x_9, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1(x_1, x_2, x_5, x_3, x_4, x_25, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_withRecApps___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_create(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_getLocalInstances(x_1, x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_saveState___rarg(x_2, x_3, x_4, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_6);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
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
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_create___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_WF_GuessLex_SavedLocalContext_create(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_SavedLocalContext_run___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_SavedLocalContext_run___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_SavedLocalContext_run___spec__1___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_SavedState_restore(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg___lambda__1___boxed), 7, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2___rarg), 8, 3);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_SavedLocalContext_run___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_create(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_WF_GuessLex_SavedLocalContext_create(x_6, x_7, x_8, x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set(x_14, 5, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_4);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set(x_17, 5, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_create___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_create(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = lean_expr_eqv(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = lean_expr_eqv(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_array_set(x_4, x_2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_10, x_7);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_46; lean_object* x_47; uint8_t x_64; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_9, x_16);
lean_dec(x_9);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_20 = x_12;
} else {
 lean_dec_ref(x_12);
 x_20 = lean_box(0);
}
x_46 = lean_array_get_size(x_19);
x_64 = lean_nat_dec_lt(x_4, x_46);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = l_instInhabitedBool;
x_66 = lean_box(x_65);
x_67 = l___private_Init_Util_0__outOfBounds___rarg(x_66);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_box(0);
x_47 = x_69;
goto block_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_46);
lean_dec(x_20);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_19);
x_71 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_17;
x_10 = x_71;
x_11 = lean_box(0);
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_array_fget(x_19, x_4);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_47 = x_75;
goto block_63;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_46);
lean_dec(x_20);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_18);
lean_ctor_set(x_76, 1, x_19);
x_77 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_17;
x_10 = x_77;
x_11 = lean_box(0);
x_12 = x_76;
goto _start;
}
}
block_45:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_21);
x_22 = lean_array_fget(x_1, x_4);
x_23 = lean_array_fget(x_1, x_10);
lean_inc(x_2);
x_24 = lean_apply_2(x_2, x_22, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_nat_add(x_18, x_16);
lean_dec(x_18);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_array_set(x_19, x_4, x_30);
x_32 = lean_box(0);
x_33 = lean_unbox(x_27);
lean_dec(x_27);
x_34 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___lambda__1(x_33, x_10, x_28, x_31, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_17;
x_10 = x_36;
x_11 = lean_box(0);
x_12 = x_35;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_box(0);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
x_41 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___lambda__1(x_40, x_10, x_18, x_19, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_17;
x_10 = x_43;
x_11 = lean_box(0);
x_12 = x_42;
goto _start;
}
}
block_63:
{
uint8_t x_48; 
lean_dec(x_47);
x_48 = lean_nat_dec_lt(x_10, x_46);
lean_dec(x_46);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = l_instInhabitedBool;
x_50 = lean_box(x_49);
x_51 = l___private_Init_Util_0__outOfBounds___rarg(x_50);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_20);
x_53 = lean_box(0);
x_21 = x_53;
goto block_45;
}
else
{
lean_object* x_54; lean_object* x_55; 
if (lean_is_scalar(x_20)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_20;
}
lean_ctor_set(x_54, 0, x_18);
lean_ctor_set(x_54, 1, x_19);
x_55 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_17;
x_10 = x_55;
x_11 = lean_box(0);
x_12 = x_54;
goto _start;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_array_fget(x_19, x_10);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_20);
x_59 = lean_box(0);
x_21 = x_59;
goto block_45;
}
else
{
lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_20)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_20;
}
lean_ctor_set(x_60, 0, x_18);
lean_ctor_set(x_60, 1, x_19);
x_61 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_17;
x_10 = x_61;
x_11 = lean_box(0);
x_12 = x_60;
goto _start;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___boxed), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_9, x_6);
if (x_12 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_8, x_15);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_nat_add(x_9, x_15);
lean_inc(x_3);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_15);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg(x_1, x_2, x_3, x_9, x_19, x_18, x_3, x_15, x_3, x_18, lean_box(0), x_11);
lean_dec(x_18);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_16;
x_9 = x_22;
x_10 = lean_box(0);
x_11 = x_20;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_16;
x_9 = x_27;
x_10 = lean_box(0);
x_11 = x_26;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_nat_add(x_9, x_15);
lean_inc(x_3);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_15);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_30);
lean_inc(x_31);
lean_inc(x_3);
lean_inc(x_2);
x_34 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg(x_1, x_2, x_3, x_9, x_32, x_31, x_3, x_15, x_3, x_31, lean_box(0), x_33);
lean_dec(x_31);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_16;
x_9 = x_39;
x_10 = lean_box(0);
x_11 = x_38;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_9, x_6);
if (x_12 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
return x_11;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_8, x_15);
lean_dec(x_8);
x_17 = lean_array_get_size(x_4);
x_18 = lean_nat_dec_lt(x_9, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_instInhabitedBool;
x_20 = lean_box(x_19);
x_21 = l___private_Init_Util_0__outOfBounds___rarg(x_20);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_array_fget(x_1, x_9);
x_24 = lean_array_push(x_11, x_23);
x_25 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_16;
x_9 = x_25;
x_10 = lean_box(0);
x_11 = x_24;
goto _start;
}
else
{
lean_object* x_27; 
x_27 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_16;
x_9 = x_27;
x_10 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_array_fget(x_4, x_9);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_array_fget(x_1, x_9);
x_32 = lean_array_push(x_11, x_31);
x_33 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_16;
x_9 = x_33;
x_10 = lean_box(0);
x_11 = x_32;
goto _start;
}
else
{
lean_object* x_35; 
x_35 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
x_8 = x_16;
x_9 = x_35;
x_10 = lean_box(0);
goto _start;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_array_get_size(x_1);
x_4 = 0;
x_5 = lean_box(x_4);
lean_inc(x_3);
x_6 = lean_mk_array(x_3, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(1u);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_6);
lean_inc_n(x_3, 2);
x_11 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5___rarg(x_1, x_2, x_3, x_9, x_7, x_3, x_8, x_3, x_7, lean_box(0), x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_mk_empty_array_with_capacity(x_12);
lean_dec(x_12);
lean_inc(x_3);
x_15 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6___rarg(x_1, x_3, x_9, x_13, x_7, x_3, x_8, x_3, x_7, lean_box(0), x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = lean_box(x_1);
x_4 = lean_box(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__4() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = 0;
x_3 = lean_box(x_1);
x_4 = lean_box(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_array_get_size(x_11);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__1(x_1, x_2, lean_box(0), x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 4);
lean_inc(x_21);
x_22 = lean_array_get_size(x_20);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__2(x_1, x_2, lean_box(0), x_20, x_21, x_17);
lean_dec(x_21);
lean_dec(x_20);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_1, 5);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_2, 5);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
lean_inc(x_31);
lean_inc(x_29);
x_33 = l_Lean_LocalContext_isSubPrefixOf(x_29, x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_LocalContext_isSubPrefixOf(x_31, x_29, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2;
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__3;
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_29);
x_37 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__4;
return x_37;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_WF_GuessLex_filterSubsumed___closed__1;
x_3 = l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_filterSubsumed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_filterSubsumed(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PSum", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inr", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__1;
x_2 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inl", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__1;
x_2 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected expression while unpacking mutual argument", 53);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
x_13 = lean_nat_dec_lt(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__3;
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Expr_isAppOfArity(x_9, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_12);
x_18 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__5;
x_19 = l_Lean_Expr_isAppOfArity(x_9, x_18, x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
x_20 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__7;
x_21 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_20, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_26);
x_28 = lean_unsigned_to_nat(2u);
x_29 = lean_nat_sub(x_27, x_28);
lean_dec(x_27);
x_30 = lean_nat_sub(x_29, x_11);
lean_dec(x_29);
x_31 = l_Lean_Expr_getRevArg_x21(x_9, x_30);
lean_ctor_set(x_2, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_9, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_sub(x_34, x_35);
lean_dec(x_34);
x_37 = lean_nat_sub(x_36, x_11);
lean_dec(x_36);
x_38 = l_Lean_Expr_getRevArg_x21(x_9, x_37);
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_38);
goto _start;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_41, x_42);
x_44 = lean_nat_dec_lt(x_43, x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__3;
x_48 = lean_unsigned_to_nat(3u);
x_49 = l_Lean_Expr_isAppOfArity(x_40, x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_43);
x_50 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__5;
x_51 = l_Lean_Expr_isAppOfArity(x_40, x_50, x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_41);
lean_dec(x_40);
x_52 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__7;
x_53 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_52, x_3, x_4, x_5, x_6, x_7);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
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
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_40, x_58);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_nat_sub(x_59, x_60);
lean_dec(x_59);
x_62 = lean_nat_sub(x_61, x_42);
lean_dec(x_61);
x_63 = l_Lean_Expr_getRevArg_x21(x_40, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_41);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_41);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_40, x_66);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_sub(x_67, x_68);
lean_dec(x_67);
x_70 = lean_nat_sub(x_69, x_42);
lean_dec(x_69);
x_71 = l_Lean_Expr_getRevArg_x21(x_40, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_43);
x_2 = x_72;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackMutualArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PSigma", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mk", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__1;
x_2 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected expression while unpacking n-ary argument", 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_array_get_size(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_dec_lt(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__3;
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Expr_isAppOfArity(x_10, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec(x_9);
x_19 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__5;
x_20 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_19, x_3, x_4, x_5, x_6, x_7);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_25);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_nat_sub(x_26, x_27);
x_29 = lean_nat_sub(x_28, x_12);
lean_dec(x_28);
lean_inc(x_10);
x_30 = l_Lean_Expr_getRevArg_x21(x_10, x_29);
x_31 = lean_array_push(x_9, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_sub(x_26, x_32);
lean_dec(x_26);
x_34 = lean_nat_sub(x_33, x_12);
lean_dec(x_33);
x_35 = l_Lean_Expr_getRevArg_x21(x_10, x_34);
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_31);
goto _start;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_2);
x_39 = lean_array_get_size(x_37);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_39, x_40);
lean_dec(x_39);
x_42 = lean_nat_dec_lt(x_41, x_1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__3;
x_46 = lean_unsigned_to_nat(4u);
x_47 = l_Lean_Expr_isAppOfArity(x_38, x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
lean_dec(x_37);
x_48 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__5;
x_49 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_48, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_unsigned_to_nat(0u);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_38, x_54);
x_56 = lean_unsigned_to_nat(2u);
x_57 = lean_nat_sub(x_55, x_56);
x_58 = lean_nat_sub(x_57, x_40);
lean_dec(x_57);
lean_inc(x_38);
x_59 = l_Lean_Expr_getRevArg_x21(x_38, x_58);
x_60 = lean_array_push(x_37, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_sub(x_55, x_61);
lean_dec(x_55);
x_63 = lean_nat_sub(x_62, x_40);
lean_dec(x_62);
x_64 = l_Lean_Expr_getRevArg_x21(x_38, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
x_2 = x_65;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_13, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Elab_WF_unpackMutualArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_nat_dec_lt(x_13, x_8);
lean_dec(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_instInhabitedNat;
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_16);
x_18 = l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4(x_17, x_14, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_10, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_10);
lean_dec(x_13);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_array_fget(x_1, x_13);
x_29 = l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4(x_28, x_14, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set(x_10, 1, x_31);
lean_ctor_set(x_29, 0, x_10);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_10, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_10);
lean_dec(x_13);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_41 = lean_nat_dec_lt(x_39, x_8);
lean_dec(x_8);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_instInhabitedNat;
x_43 = l___private_Init_Util_0__outOfBounds___rarg(x_42);
x_44 = l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4(x_43, x_40, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
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
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
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
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_array_fget(x_1, x_39);
x_55 = l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4(x_54, x_40, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_56);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_39);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_8);
x_65 = !lean_is_exclusive(x_9);
if (x_65 == 0)
{
return x_9;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_9, 0);
x_67 = lean_ctor_get(x_9, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_9);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
x_13 = l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1(x_3, x_4, x_6, x_7, x_8, x_9, x_10);
if (x_12 == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instInhabitedExpr;
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_16);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1(x_3, x_17, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_25 = lean_ctor_get(x_8, 5);
lean_inc(x_25);
x_26 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_create(x_25, x_18, x_19, x_23, x_24, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_8);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
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
lean_dec(x_8);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_array_fget(x_1, x_2);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1(x_3, x_37, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_ctor_get(x_8, 5);
lean_inc(x_45);
x_46 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_create(x_45, x_38, x_39, x_43, x_44, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_8);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_8);
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
lean_dec(x_8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Insufficient arguments in recursive call", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_le(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__2;
x_15 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__1(x_4, x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
lean_dec(x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2), 9, 2);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_4);
if (x_13 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_instInhabitedExpr;
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_16);
x_18 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg(x_14, x_2, x_17, x_5, x_15, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_1, x_2);
x_20 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg(x_14, x_2, x_19, x_5, x_15, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unexpected number of lambdas in unary pre-definition", 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__2;
x_16 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_15, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__3(x_4, x_1, x_2, x_3, x_5, x_21, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
x_9 = l_Lean_Elab_addAsAxiom(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4), 10, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_11, x_12, x_4, x_5, x_6, x_7, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__5), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_withoutModifyingState___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__6(x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackMutualArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_unpackMutualArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_unpackUnaryArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_unpackArg___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toCtorIdx(uint8_t x_1) {
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
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.WF.GuessLex.GuessLexRel.lt", 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__4;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__7;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.WF.GuessLex.GuessLexRel.eq", 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__10;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.WF.GuessLex.GuessLexRel.le", 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__17;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__16;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__19;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.WF.GuessLex.GuessLexRel.no_idea", 41);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__21;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__22;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__23;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6;
x_2 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__22;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__26() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__25;
x_2 = 0;
x_3 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322_(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1024u);
x_4 = lean_nat_dec_le(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__5;
x_6 = l_Repr_addAppParen(x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__8;
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
case 1:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(1024u);
x_10 = lean_nat_dec_le(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__12;
x_12 = l_Repr_addAppParen(x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__14;
x_14 = l_Repr_addAppParen(x_13, x_2);
return x_14;
}
}
case 2:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__18;
x_18 = l_Repr_addAppParen(x_17, x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__20;
x_20 = l_Repr_addAppParen(x_19, x_2);
return x_20;
}
}
default: 
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__24;
x_24 = l_Repr_addAppParen(x_23, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__26;
x_26 = l_Repr_addAppParen(x_25, x_2);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instReprGuessLexRel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instReprGuessLexRel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_WF_GuessLex_instReprGuessLexRel___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_WF_GuessLex_GuessLexRel_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_1, x_2);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 3;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toCtorIdx(x_1);
x_4 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("≤", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\?", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3;
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4;
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LT", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__1;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__3;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instLTNat", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__12;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__13;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__11;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__5;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__14;
x_3 = l_Lean_mkAppN(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__17;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__18;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__19;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__21;
x_3 = l_Lean_mkAppN(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LE", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__23;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__24;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__25;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__4;
x_3 = l_Lean_Expr_const___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instLENat", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__27;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__28;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__13;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__29;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__26;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__30;
x_3 = l_Lean_mkAppN(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.PreDefinition.WF.GuessLex", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.WF.GuessLex.GuessLexRel.toNatRel", 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__32;
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__33;
x_3 = lean_unsigned_to_nat(306u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__34;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__15;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__22;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__31;
return x_4;
}
default: 
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__35;
x_6 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SizeOf", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sizeOf", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__1;
x_2 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_mkSizeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Meta_getLevel(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__2;
lean_inc(x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_14);
x_17 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
lean_inc(x_8);
x_18 = lean_array_push(x_17, x_8);
x_19 = l_Lean_mkAppN(x_16, x_18);
x_20 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Meta_synthInstance(x_19, x_20, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4;
x_25 = l_Lean_Expr_const___override(x_24, x_14);
x_26 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__5;
x_27 = lean_array_push(x_26, x_8);
x_28 = lean_array_push(x_27, x_22);
x_29 = lean_array_push(x_28, x_1);
x_30 = l_Lean_mkAppN(x_25, x_29);
lean_inc(x_30);
x_31 = l_Lean_Meta_check(x_30, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_30);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_7);
if (x_48 == 0)
{
return x_7;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_reportUnsolvedGoals(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_2 = x_13;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_Elab_Term_reportUnsolvedGoals(x_23, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_2 = x_22;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_29 = x_24;
} else {
 lean_dec_ref(x_24);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_box(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inspectRecCall: success!", 24);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
lean_inc(x_1);
x_9 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__1(x_2, x_13, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__2;
x_17 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_16, x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__1(x_2, x_18, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_18);
return x_20;
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__4(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tacticDecreasing_tactic", 23);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decreasing_tactic", 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_7, 5);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
x_13 = lean_st_ref_get(x_8, x_9);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__3;
lean_inc(x_12);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__2;
x_18 = l_Lean_Syntax_node1(x_12, x_17, x_16);
x_19 = l_Lean_Elab_Tactic_evalTactic(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_Tactic_run(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_List_forM___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__1(x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Term_runTactic(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Did not find ", 13);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" proof: ", 8);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__8() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__7;
x_3 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__6;
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
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__4___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = 1;
x_5 = 0;
x_6 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__8;
x_7 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__9;
x_8 = lean_alloc_ctor(0, 8, 9);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
lean_ctor_set(x_8, 5, x_2);
lean_ctor_set(x_8, 6, x_2);
lean_ctor_set(x_8, 7, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 1, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 2, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 3, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 4, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 5, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 6, x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 7, x_4);
lean_ctor_set_uint8(x_8, sizeof(void*)*8 + 8, x_5);
return x_8;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_45; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_45 = l_Lean_Meta_check(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
lean_inc(x_7);
x_48 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_47, x_7, x_8, x_9, x_10, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Expr_mvarId_x21(x_49);
x_52 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_53 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_54 = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(x_51, x_52, x_53, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = 1;
x_59 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_3, x_58);
if (x_59 == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_box(0);
x_123 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__12;
lean_inc(x_55);
x_124 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__6), 10, 3);
lean_closure_set(x_124, 0, x_55);
lean_closure_set(x_124, 1, x_123);
lean_closure_set(x_124, 2, x_122);
x_125 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__10;
x_126 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__11;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_127 = l_Lean_Elab_Term_TermElabM_run___rarg(x_124, x_125, x_126, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_57);
lean_dec(x_55);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2(x_2, x_3, x_130, x_7, x_8, x_9, x_10, x_129);
x_12 = x_131;
goto block_44;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 1);
lean_inc(x_133);
lean_dec(x_127);
x_60 = x_132;
x_61 = x_133;
goto block_121;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_5, 0);
lean_inc(x_134);
lean_dec(x_5);
lean_inc(x_55);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_55);
lean_inc(x_55);
x_136 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__7), 10, 3);
lean_closure_set(x_136, 0, x_135);
lean_closure_set(x_136, 1, x_55);
lean_closure_set(x_136, 2, x_134);
x_137 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutErrToSorry___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__2), 8, 1);
lean_closure_set(x_137, 0, x_136);
x_138 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__10;
x_139 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__11;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_140 = l_Lean_Elab_Term_TermElabM_run___rarg(x_137, x_138, x_139, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_57);
lean_dec(x_55);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2(x_2, x_3, x_143, x_7, x_8, x_9, x_10, x_142);
x_12 = x_144;
goto block_44;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_140, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_60 = x_145;
x_61 = x_146;
goto block_121;
}
}
}
else
{
lean_object* x_147; 
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_55);
x_147 = l_Lean_MVarId_refl(x_55, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_57);
lean_dec(x_55);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2(x_2, x_3, x_148, x_7, x_8, x_9, x_10, x_149);
x_12 = x_150;
goto block_44;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 1);
lean_inc(x_152);
lean_dec(x_147);
x_60 = x_151;
x_61 = x_152;
goto block_121;
}
}
block_121:
{
uint8_t x_62; 
x_62 = l_Lean_Exception_isRuntime(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_60);
lean_dec(x_57);
lean_inc(x_2);
x_63 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_7, x_8, x_9, x_10, x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__1;
x_67 = lean_unbox(x_64);
lean_dec(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = lean_apply_6(x_66, x_68, x_7, x_8, x_9, x_10, x_65);
x_12 = x_69;
goto block_44;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Elab_goalsToMessageData(x_71);
switch (x_3) {
case 0:
{
lean_object* x_87; 
x_87 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1;
x_73 = x_87;
goto block_86;
}
case 1:
{
lean_object* x_88; 
x_88 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2;
x_73 = x_88;
goto block_86;
}
case 2:
{
lean_object* x_89; 
x_89 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3;
x_73 = x_89;
goto block_86;
}
default: 
{
lean_object* x_90; 
x_90 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4;
x_73 = x_90;
goto block_86;
}
}
block_86:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__3;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__5;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_72);
x_80 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_81, x_7, x_8, x_9, x_10, x_65);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_apply_6(x_66, x_83, x_7, x_8, x_9, x_10, x_84);
x_12 = x_85;
goto block_44;
}
}
}
else
{
uint8_t x_91; 
x_91 = lean_ctor_get_uint8(x_9, sizeof(void*)*11);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_57)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_57;
 lean_ctor_set_tag(x_92, 1);
}
lean_ctor_set(x_92, 0, x_60);
lean_ctor_set(x_92, 1, x_61);
x_12 = x_92;
goto block_44;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_60);
lean_dec(x_57);
lean_inc(x_2);
x_93 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_7, x_8, x_9, x_10, x_61);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__1;
x_97 = lean_unbox(x_94);
lean_dec(x_94);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_55);
lean_dec(x_2);
x_98 = lean_box(0);
x_99 = lean_apply_6(x_96, x_98, x_7, x_8, x_9, x_10, x_95);
x_12 = x_99;
goto block_44;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_55);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Elab_goalsToMessageData(x_101);
switch (x_3) {
case 0:
{
lean_object* x_117; 
x_117 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1;
x_103 = x_117;
goto block_116;
}
case 1:
{
lean_object* x_118; 
x_118 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2;
x_103 = x_118;
goto block_116;
}
case 2:
{
lean_object* x_119; 
x_119 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3;
x_103 = x_119;
goto block_116;
}
default: 
{
lean_object* x_120; 
x_120 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4;
x_103 = x_120;
goto block_116;
}
}
block_116:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__3;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__5;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_102);
x_110 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_111, x_7, x_8, x_9, x_10, x_95);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_apply_6(x_96, x_113, x_7, x_8, x_9, x_10, x_114);
x_12 = x_115;
goto block_44;
}
}
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_54);
if (x_153 == 0)
{
return x_54;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_54, 0);
x_155 = lean_ctor_get(x_54, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_54);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_45);
if (x_157 == 0)
{
return x_45;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_45, 0);
x_159 = lean_ctor_get(x_45, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_45);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
block_44:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
switch (lean_obj_tag(x_13)) {
case 0:
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
case 1:
{
uint8_t x_28; 
lean_dec(x_13);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_12, 0);
lean_dec(x_29);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_12, 0, x_30);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
default: 
{
uint8_t x_34; 
lean_dec(x_13);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_12, 0);
lean_dec(x_35);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_4);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Goal for ", 9);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_unbox(x_16);
x_19 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel(x_18);
x_20 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__12;
lean_inc(x_5);
x_21 = lean_array_push(x_20, x_5);
lean_inc(x_6);
x_22 = lean_array_push(x_21, x_6);
x_23 = l_Lean_mkAppN(x_19, x_22);
lean_inc(x_2);
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_10, x_11, x_12, x_13, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_unbox(x_16);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_2);
x_30 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8(x_23, x_2, x_29, x_7, x_1, x_28, x_10, x_11, x_12, x_13, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_ctor_set(x_30, 0, x_34);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_8 = x_17;
x_9 = x_39;
x_14 = x_38;
goto _start;
}
}
else
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_76; 
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
lean_inc(x_23);
x_46 = l_Lean_MessageData_ofExpr(x_23);
x_76 = lean_unbox(x_16);
switch (x_76) {
case 0:
{
lean_object* x_77; 
x_77 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1;
x_47 = x_77;
goto block_75;
}
case 1:
{
lean_object* x_78; 
x_78 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2;
x_47 = x_78;
goto block_75;
}
case 2:
{
lean_object* x_79; 
x_79 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3;
x_47 = x_79;
goto block_75;
}
default: 
{
lean_object* x_80; 
x_80 = l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4;
x_47 = x_80;
goto block_75;
}
}
block_75:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__2;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__4;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_2);
x_56 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_55, x_10, x_11, x_12, x_13, x_45);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_unbox(x_16);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_2);
x_60 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8(x_23, x_2, x_59, x_7, x_1, x_57, x_10, x_11, x_12, x_13, x_58);
lean_dec(x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec(x_61);
lean_ctor_set(x_60, 0, x_64);
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_dec(x_60);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
lean_dec(x_61);
x_8 = x_17;
x_9 = x_69;
x_14 = x_68;
goto _start;
}
}
else
{
uint8_t x_71; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_60);
if (x_71 == 0)
{
return x_60;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_60, 0);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_60);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 3;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__2;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4() {
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
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Elab_WF_GuessLex_mkSizeOf(x_1, x_8, x_9, x_10, x_11, x_12);
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
x_16 = l_Lean_Elab_WF_GuessLex_mkSizeOf(x_2, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__3;
x_20 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3(x_3, x_4, x_5, x_6, x_14, x_17, x_20, x_19, x_20, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__5;
x_26 = lean_box(0);
x_27 = lean_apply_6(x_25, x_26, x_8, x_9, x_10, x_11, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inspectRecCall: ", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" (", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(") → ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2(x_2, x_3, x_4, x_1, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
x_21 = l_Nat_repr(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_3);
x_28 = l_Lean_MessageData_ofExpr(x_3);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__6;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_ctor_get(x_7, 3);
lean_inc(x_32);
lean_dec(x_7);
x_33 = l_Nat_repr(x_32);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
lean_inc(x_2);
x_38 = l_Lean_MessageData_ofExpr(x_2);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__8;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_1);
x_42 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_41, x_8, x_9, x_10, x_11, x_19);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2(x_2, x_3, x_4, x_1, x_5, x_6, x_43, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_43);
return x_45;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_evalRecCall___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_4, x_15);
lean_dec(x_15);
x_17 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3;
if (x_13 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
x_31 = l_Lean_instInhabitedExpr;
x_32 = l___private_Init_Util_0__outOfBounds___rarg(x_31);
x_18 = x_32;
goto block_30;
}
else
{
lean_object* x_33; 
x_33 = lean_array_fget(x_11, x_3);
lean_dec(x_11);
x_18 = x_33;
goto block_30;
}
block_30:
{
if (x_16 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_19 = l_Lean_instInhabitedExpr;
x_20 = l___private_Init_Util_0__outOfBounds___rarg(x_19);
x_21 = l_Lean_Elab_WF_GuessLex_evalRecCall___closed__1;
x_22 = l_Lean_Elab_WF_GuessLex_evalRecCall___closed__2;
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___boxed), 12, 7);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_18);
lean_closure_set(x_23, 3, x_1);
lean_closure_set(x_23, 4, x_21);
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_2);
x_24 = l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg(x_10, x_23, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_array_fget(x_14, x_4);
lean_dec(x_14);
x_26 = l_Lean_Elab_WF_GuessLex_evalRecCall___closed__1;
x_27 = l_Lean_Elab_WF_GuessLex_evalRecCall___closed__2;
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___boxed), 12, 7);
lean_closure_set(x_28, 0, x_17);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_18);
lean_closure_set(x_28, 3, x_1);
lean_closure_set(x_28, 4, x_26);
lean_closure_set(x_28, 5, x_27);
lean_closure_set(x_28, 6, x_2);
x_29 = l_Lean_Elab_WF_GuessLex_SavedLocalContext_run___rarg(x_10, x_28, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__1(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__4___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__4(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_evalRecCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_WF_GuessLex_evalRecCall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_mk(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
lean_dec(x_4);
x_6 = lean_ctor_get(x_2, 4);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_mk_array(x_5, x_9);
x_11 = lean_st_mk_ref(x_10, x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_46 = lean_box(0);
x_47 = lean_array_get_size(x_12);
x_48 = lean_nat_dec_lt(x_2, x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_12);
x_49 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_50 = l___private_Init_Util_0__outOfBounds___rarg(x_49);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_3, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
x_53 = l___private_Init_Util_0__outOfBounds___rarg(x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_free_object(x_10);
x_54 = lean_box(0);
x_14 = x_54;
goto block_45;
}
else
{
lean_object* x_55; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
lean_ctor_set(x_10, 0, x_55);
return x_10;
}
}
else
{
lean_object* x_56; 
x_56 = lean_array_fget(x_50, x_3);
lean_dec(x_50);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_free_object(x_10);
x_57 = lean_box(0);
x_14 = x_57;
goto block_45;
}
else
{
lean_object* x_58; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
lean_ctor_set(x_10, 0, x_58);
return x_10;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_array_fget(x_12, x_2);
lean_dec(x_12);
x_60 = lean_array_get_size(x_59);
x_61 = lean_nat_dec_lt(x_3, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_59);
x_62 = l___private_Init_Util_0__outOfBounds___rarg(x_46);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_free_object(x_10);
x_63 = lean_box(0);
x_14 = x_63;
goto block_45;
}
else
{
lean_object* x_64; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
lean_ctor_set(x_10, 0, x_64);
return x_10;
}
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget(x_59, x_3);
lean_dec(x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
lean_free_object(x_10);
x_66 = lean_box(0);
x_14 = x_66;
goto block_45;
}
else
{
lean_object* x_67; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
lean_ctor_set(x_10, 0, x_67);
return x_10;
}
}
}
block_45:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Elab_WF_GuessLex_evalRecCall(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_9, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_21);
x_24 = lean_nat_dec_lt(x_2, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_st_ref_set(x_9, x_21, x_22);
lean_dec(x_9);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_18);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_30 = lean_array_fget(x_21, x_2);
x_31 = lean_box(0);
x_32 = lean_array_fset(x_21, x_2, x_31);
lean_inc(x_18);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_18);
x_34 = lean_array_set(x_30, x_3, x_33);
x_35 = lean_array_fset(x_32, x_2, x_34);
x_36 = lean_st_ref_set(x_9, x_35, x_22);
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_18);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_68 = lean_ctor_get(x_10, 0);
x_69 = lean_ctor_get(x_10, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_10);
x_100 = lean_box(0);
x_101 = lean_array_get_size(x_68);
x_102 = lean_nat_dec_lt(x_2, x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_68);
x_103 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_104 = l___private_Init_Util_0__outOfBounds___rarg(x_103);
x_105 = lean_array_get_size(x_104);
x_106 = lean_nat_dec_lt(x_3, x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_104);
x_107 = l___private_Init_Util_0__outOfBounds___rarg(x_100);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_box(0);
x_70 = x_108;
goto block_99;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_69);
return x_110;
}
}
else
{
lean_object* x_111; 
x_111 = lean_array_fget(x_104, x_3);
lean_dec(x_104);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_box(0);
x_70 = x_112;
goto block_99;
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_69);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_array_fget(x_68, x_2);
lean_dec(x_68);
x_116 = lean_array_get_size(x_115);
x_117 = lean_nat_dec_lt(x_3, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_115);
x_118 = l___private_Init_Util_0__outOfBounds___rarg(x_100);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_box(0);
x_70 = x_119;
goto block_99;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_69);
return x_121;
}
}
else
{
lean_object* x_122; 
x_122 = lean_array_fget(x_115, x_3);
lean_dec(x_115);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_box(0);
x_70 = x_123;
goto block_99;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_69);
return x_125;
}
}
}
block_99:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_70);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
lean_dec(x_1);
x_73 = l_Lean_Elab_WF_GuessLex_evalRecCall(x_71, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_69);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_st_ref_take(x_9, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_lt(x_2, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_st_ref_set(x_9, x_77, x_78);
lean_dec(x_9);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_array_fget(x_77, x_2);
x_86 = lean_box(0);
x_87 = lean_array_fset(x_77, x_2, x_86);
lean_inc(x_74);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_74);
x_89 = lean_array_set(x_85, x_3, x_88);
x_90 = lean_array_fset(x_87, x_2, x_89);
x_91 = lean_st_ref_set(x_9, x_90, x_78);
lean_dec(x_9);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_74);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_9);
x_95 = lean_ctor_get(x_73, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_73, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_97 = x_73;
} else {
 lean_dec_ref(x_73);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_RecCallCache_eval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_45; uint8_t x_46; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_st_ref_get(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_box(0);
x_45 = lean_array_get_size(x_11);
x_46 = lean_nat_dec_lt(x_2, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
x_47 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_48 = l___private_Init_Util_0__outOfBounds___rarg(x_47);
x_15 = x_48;
goto block_44;
}
else
{
lean_object* x_49; 
x_49 = lean_array_fget(x_11, x_2);
lean_dec(x_11);
x_15 = x_49;
goto block_44;
}
block_44:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_15);
x_17 = lean_nat_dec_lt(x_3, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
x_18 = l___private_Init_Util_0__outOfBounds___rarg(x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___closed__1;
if (lean_is_scalar(x_13)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_13;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
switch (x_22) {
case 0:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1;
if (lean_is_scalar(x_13)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_13;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
case 1:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2;
if (lean_is_scalar(x_13)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_13;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
case 2:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3;
if (lean_is_scalar(x_13)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_13;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4;
if (lean_is_scalar(x_13)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_13;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
return x_30;
}
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_array_fget(x_15, x_3);
lean_dec(x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___closed__1;
if (lean_is_scalar(x_13)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_13;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_12);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
switch (x_35) {
case 0:
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1;
if (lean_is_scalar(x_13)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_13;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
case 1:
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2;
if (lean_is_scalar(x_13)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_13;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_12);
return x_39;
}
case 2:
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3;
if (lean_is_scalar(x_13)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_13;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
default: 
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4;
if (lean_is_scalar(x_13)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_13;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
return x_43;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_inspectCall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_9, 1);
x_11 = lean_nat_dec_eq(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = lean_nat_dec_eq(x_12, x_2);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_17 = 3;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_inspectCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_lt(x_10, x_11);
x_13 = lean_ctor_get(x_9, 3);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_nat_dec_lt(x_13, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_15 = l_instInhabitedNat;
x_16 = l___private_Init_Util_0__outOfBounds___rarg(x_15);
if (x_14 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_8);
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_15);
x_18 = l_Lean_Elab_WF_GuessLex_RecCallCache_eval(x_1, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_17);
lean_dec(x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_8, x_13);
lean_dec(x_13);
lean_dec(x_8);
x_20 = l_Lean_Elab_WF_GuessLex_RecCallCache_eval(x_1, x_16, x_19, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_19);
lean_dec(x_16);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_array_fget(x_8, x_10);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_8);
x_22 = l_instInhabitedNat;
x_23 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
x_24 = l_Lean_Elab_WF_GuessLex_RecCallCache_eval(x_1, x_21, x_23, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_23);
lean_dec(x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_array_fget(x_8, x_13);
lean_dec(x_13);
lean_dec(x_8);
x_26 = l_Lean_Elab_WF_GuessLex_RecCallCache_eval(x_1, x_21, x_25, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_25);
lean_dec(x_21);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_nat_dec_eq(x_29, x_27);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_WF_GuessLex_inspectCall___lambda__1(x_1, x_27, x_31, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_27);
lean_dec(x_1);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 3);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_nat_dec_eq(x_33, x_27);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l_Lean_Elab_WF_GuessLex_inspectCall___lambda__1(x_1, x_27, x_38, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_27);
lean_dec(x_1);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_inspectCall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_inspectCall___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_16 = x_4;
} else {
 lean_dec_ref(x_4);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_16)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_16;
}
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_24 = lean_ctor_get(x_14, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_14, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_14, 0);
lean_dec(x_26);
x_27 = lean_nat_add(x_17, x_19);
lean_ctor_set(x_14, 0, x_27);
x_44 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
x_45 = lean_array_push(x_44, x_13);
x_46 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_47 = l_Lean_Meta_mkAppM(x_46, x_45, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_Meta_whnfD(x_48, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_16);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Expr_isLit(x_51);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; size_t x_55; size_t x_56; 
lean_dec(x_17);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_14);
lean_ctor_set(x_54, 1, x_15);
x_55 = 1;
x_56 = lean_usize_add(x_3, x_55);
x_3 = x_56;
x_4 = x_54;
x_9 = x_52;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
x_58 = lean_array_push(x_15, x_17);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
x_60 = 1;
x_61 = lean_usize_add(x_3, x_60);
x_3 = x_61;
x_4 = x_59;
x_9 = x_52;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_dec(x_50);
x_28 = x_63;
x_29 = x_64;
goto block_43;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_47, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
lean_dec(x_47);
x_28 = x_65;
x_29 = x_66;
goto block_43;
}
block_43:
{
uint8_t x_30; 
x_30 = l_Lean_Exception_isRuntime(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
lean_dec(x_28);
x_31 = lean_array_push(x_15, x_17);
if (lean_is_scalar(x_16)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_16;
}
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_31);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
x_4 = x_32;
x_9 = x_29;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
lean_dec(x_28);
x_38 = lean_array_push(x_15, x_17);
if (lean_is_scalar(x_16)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_16;
}
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_38);
x_40 = 1;
x_41 = lean_usize_add(x_3, x_40);
x_3 = x_41;
x_4 = x_39;
x_9 = x_29;
goto _start;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_14);
x_67 = lean_nat_add(x_17, x_19);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_18);
lean_ctor_set(x_68, 2, x_19);
x_85 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
x_86 = lean_array_push(x_85, x_13);
x_87 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_88 = l_Lean_Meta_mkAppM(x_87, x_86, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_91 = l_Lean_Meta_whnfD(x_89, x_5, x_6, x_7, x_8, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_16);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Expr_isLit(x_92);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; size_t x_96; size_t x_97; 
lean_dec(x_17);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_68);
lean_ctor_set(x_95, 1, x_15);
x_96 = 1;
x_97 = lean_usize_add(x_3, x_96);
x_3 = x_97;
x_4 = x_95;
x_9 = x_93;
goto _start;
}
else
{
lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; 
x_99 = lean_array_push(x_15, x_17);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_68);
lean_ctor_set(x_100, 1, x_99);
x_101 = 1;
x_102 = lean_usize_add(x_3, x_101);
x_3 = x_102;
x_4 = x_100;
x_9 = x_93;
goto _start;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_91, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
lean_dec(x_91);
x_69 = x_104;
x_70 = x_105;
goto block_84;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_88, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_88, 1);
lean_inc(x_107);
lean_dec(x_88);
x_69 = x_106;
x_70 = x_107;
goto block_84;
}
block_84:
{
uint8_t x_71; 
x_71 = l_Lean_Exception_isRuntime(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; 
lean_dec(x_69);
x_72 = lean_array_push(x_15, x_17);
if (lean_is_scalar(x_16)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_16;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
x_74 = 1;
x_75 = lean_usize_add(x_3, x_74);
x_3 = x_75;
x_4 = x_73;
x_9 = x_70;
goto _start;
}
else
{
uint8_t x_77; 
x_77 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_68);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_70);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; 
lean_dec(x_69);
x_79 = lean_array_push(x_15, x_17);
if (lean_is_scalar(x_16)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_16;
}
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_79);
x_81 = 1;
x_82 = lean_usize_add(x_3, x_81);
x_3 = x_82;
x_4 = x_80;
x_9 = x_70;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_toSubarray___rarg(x_2, x_1, x_13);
x_15 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___spec__1(x_14, x_18, x_20, x_16, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_isForbidden(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_isForbidden___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_isForbidden(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
lean_dec(x_1);
x_8 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform(x_2, x_3, x_7, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_24; uint8_t x_25; 
x_5 = lean_array_get_size(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_5);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_6 = x_26;
goto block_23;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_5);
x_29 = l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__2(x_3, x_2, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_6 = x_30;
goto block_23;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
}
block_23:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_dec(x_6);
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_inc(x_3);
x_10 = lean_mk_array(x_5, x_3);
x_11 = lean_array_push(x_4, x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___lambda__1(x_3, x_1, x_2, x_12, x_11);
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_16 = l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__1(x_3, x_1, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_3);
x_17 = lean_mk_array(x_5, x_3);
x_18 = lean_array_push(x_4, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___lambda__1(x_3, x_1, x_2, x_19, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___lambda__1(x_3, x_1, x_2, x_21, x_4);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_3, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_instInhabitedNat;
x_11 = l___private_Init_Util_0__outOfBounds___rarg(x_10);
x_12 = lean_nat_dec_eq(x_7, x_11);
lean_dec(x_11);
lean_dec(x_7);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_1, x_8);
x_18 = lean_nat_dec_eq(x_7, x_17);
lean_dec(x_17);
lean_dec(x_7);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_4 = x_21;
goto _start;
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_9);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_isForbidden(x_1, x_4, x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_nat_add(x_4, x_15);
lean_inc(x_6);
lean_inc(x_10);
x_19 = lean_array_push(x_10, x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go(x_1, x_2, x_3, x_18, x_19, x_11);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_30 = lean_box(0);
x_5 = x_16;
x_6 = x_29;
x_9 = x_30;
x_11 = x_28;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_33 = lean_box(0);
x_5 = x_16;
x_6 = x_32;
x_9 = x_33;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_array_get_size(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1(x_3, x_12, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_9);
x_16 = l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__1(x_5, x_9, x_5, x_14, x_15);
lean_dec(x_9);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1(x_3, x_17, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_5);
x_19 = lean_array_push(x_6, x_5);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1(x_3, x_20, x_5, x_19);
lean_dec(x_5);
lean_dec(x_3);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_fget(x_2, x_4);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_box(0);
lean_inc(x_22);
x_26 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__2(x_1, x_2, x_3, x_4, x_22, x_23, x_22, x_24, x_25, x_5, x_6);
lean_dec(x_22);
lean_dec(x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_27);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 0);
lean_dec(x_35);
x_36 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1;
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_dec(x_26);
x_38 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__1(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateCombinations_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform(x_1, x_2, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Too many combinations", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_generateMeasures___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__4() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_generateMeasures___closed__3;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateMeasures(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_unsigned_to_nat(32u);
lean_inc(x_2);
x_9 = l_Lean_Elab_WF_GuessLex_generateCombinations_x3f(x_1, x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_array_get_size(x_2);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_array_get_size(x_10);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__2(x_15, x_16, x_10);
if (x_13 == 0)
{
size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
x_18 = l_Lean_Elab_WF_GuessLex_generateMeasures___closed__4;
x_19 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__3(x_18, x_16, x_19);
x_21 = l_Array_append___rarg(x_17, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = l_List_range(x_11);
x_24 = l_List_redLength___rarg(x_23);
x_25 = lean_mk_empty_array_with_capacity(x_24);
lean_dec(x_24);
x_26 = l_List_toArrayAux___rarg(x_23, x_25);
x_27 = lean_array_get_size(x_26);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__3(x_28, x_16, x_26);
x_30 = l_Array_append___rarg(x_17, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_generateMeasures___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_generateMeasures___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_GuessLex_generateMeasures(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; 
x_8 = 0;
x_9 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_array_push(x_1, x_2);
x_11 = 2;
x_12 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_7, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = 1;
x_14 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_10);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_apply_2(x_16, lean_box(0), x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
lean_inc(x_24);
x_26 = lean_apply_2(x_24, lean_box(0), x_25);
x_27 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_27, 0, x_4);
lean_closure_set(x_27, 1, x_10);
lean_closure_set(x_27, 2, x_5);
lean_closure_set(x_27, 3, x_24);
x_28 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_26, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
lean_dec(x_3);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
lean_inc(x_30);
x_32 = lean_apply_2(x_30, lean_box(0), x_31);
x_33 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_33, 0, x_4);
lean_closure_set(x_33, 1, x_10);
lean_closure_set(x_33, 2, x_5);
lean_closure_set(x_33, 3, x_30);
x_34 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_32, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
lean_dec(x_2);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
lean_inc(x_36);
x_38 = lean_apply_2(x_36, lean_box(0), x_37);
x_39 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_5);
lean_closure_set(x_39, 2, x_36);
x_40 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_38, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_14, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_6, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_array_uget(x_4, x_6);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_array_uget(x_4, x_6);
lean_inc(x_3);
x_19 = lean_apply_1(x_18, x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_12);
lean_closure_set(x_20, 2, x_1);
lean_closure_set(x_20, 3, x_16);
lean_closure_set(x_20, 4, x_15);
lean_closure_set(x_20, 5, x_2);
lean_inc(x_2);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_box_usize(x_6);
x_23 = lean_box_usize(x_5);
x_24 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__4___boxed), 7, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_23);
x_25 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Array_eraseIdx___rarg(x_1, x_2);
x_10 = lean_array_push(x_3, x_4);
lean_inc(x_5);
x_11 = l_Lean_Elab_WF_GuessLex_solve_go___rarg(x_5, x_9, x_6, x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__1), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_4);
lean_closure_set(x_23, 2, x_5);
lean_closure_set(x_23, 3, x_6);
lean_closure_set(x_23, 4, x_1);
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_7);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_apply_2(x_25, lean_box(0), x_26);
x_28 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_27, x_23);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
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
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_apply_2(x_17, lean_box(0), x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_21 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_3, x_13, x_20, lean_box(0), x_19);
lean_dec(x_13);
return x_21;
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_13, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
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
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_15);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_12, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_12, x_22);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_array_fget(x_2, x_13);
x_26 = lean_array_get_size(x_3);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__2;
lean_inc(x_3);
lean_inc(x_25);
lean_inc(x_5);
lean_inc(x_1);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg(x_1, x_5, x_25, x_3, x_27, x_28, x_29);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_8);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__3), 8, 7);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_8);
lean_closure_set(x_31, 2, x_2);
lean_closure_set(x_31, 3, x_13);
lean_closure_set(x_31, 4, x_4);
lean_closure_set(x_31, 5, x_25);
lean_closure_set(x_31, 6, x_5);
lean_inc(x_5);
x_32 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_30, x_31);
x_33 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__4), 14, 13);
lean_closure_set(x_33, 0, x_1);
lean_closure_set(x_33, 1, x_13);
lean_closure_set(x_33, 2, x_11);
lean_closure_set(x_33, 3, x_2);
lean_closure_set(x_33, 4, x_3);
lean_closure_set(x_33, 5, x_4);
lean_closure_set(x_33, 6, x_5);
lean_closure_set(x_33, 7, x_6);
lean_closure_set(x_33, 8, x_7);
lean_closure_set(x_33, 9, x_8);
lean_closure_set(x_33, 10, x_9);
lean_closure_set(x_33, 11, x_10);
lean_closure_set(x_33, 12, x_23);
x_34 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_32, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
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
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_apply_2(x_36, lean_box(0), x_15);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___boxed), 15, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4;
lean_inc_n(x_7, 2);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg(x_1, x_2, x_3, x_4, x_6, x_7, x_10, x_12, x_8, x_7, x_9, x_7, x_8, lean_box(0), x_12);
lean_dec(x_7);
lean_inc(x_6);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__2), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_6);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__3___boxed), 5, 4);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
x_6 = l_Array_isEmpty___rarg(x_3);
lean_dec(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_solve_go___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___lambda__4(x_1, x_8, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_WF_GuessLex_solve_go___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_5 = l_Lean_Elab_WF_GuessLex_solve_go___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_solve___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tuple", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6;
x_2 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__1;
x_3 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__2;
x_4 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 5);
lean_inc(x_12);
lean_dec(x_4);
x_13 = 0;
x_14 = l_Lean_SourceInfo_fromRef(x_12, x_13);
x_15 = lean_st_ref_get(x_5, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5;
lean_inc(x_14);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
x_21 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8;
lean_inc(x_14);
x_22 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_get_size(x_1);
lean_inc(x_1);
x_24 = l_Array_toSubarray___rarg(x_1, x_10, x_23);
x_25 = l_Array_ofSubarray___rarg(x_24);
x_26 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__9;
x_27 = l_Lean_mkSepArray(x_25, x_26);
lean_dec(x_25);
x_28 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_29 = l_Array_append___rarg(x_28, x_27);
x_30 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7;
lean_inc(x_14);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_29);
x_32 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7;
lean_inc(x_14);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_32);
if (x_20 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = l___private_Init_Util_0__outOfBounds___rarg(x_34);
lean_inc(x_14);
x_36 = l_Lean_Syntax_node3(x_14, x_30, x_35, x_22, x_31);
x_37 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4;
x_38 = l_Lean_Syntax_node3(x_14, x_37, x_19, x_36, x_33);
lean_ctor_set(x_15, 0, x_38);
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_array_fget(x_1, x_8);
lean_dec(x_1);
lean_inc(x_14);
x_40 = l_Lean_Syntax_node3(x_14, x_30, x_39, x_22, x_31);
x_41 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4;
x_42 = l_Lean_Syntax_node3(x_14, x_41, x_19, x_40, x_33);
lean_ctor_set(x_15, 0, x_42);
return x_15;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_dec(x_15);
x_44 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5;
lean_inc(x_14);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_14);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
x_47 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8;
lean_inc(x_14);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_array_get_size(x_1);
lean_inc(x_1);
x_50 = l_Array_toSubarray___rarg(x_1, x_10, x_49);
x_51 = l_Array_ofSubarray___rarg(x_50);
x_52 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__9;
x_53 = l_Lean_mkSepArray(x_51, x_52);
lean_dec(x_51);
x_54 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_55 = l_Array_append___rarg(x_54, x_53);
x_56 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7;
lean_inc(x_14);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_55);
x_58 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7;
lean_inc(x_14);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
if (x_46 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = l___private_Init_Util_0__outOfBounds___rarg(x_60);
lean_inc(x_14);
x_62 = l_Lean_Syntax_node3(x_14, x_56, x_61, x_48, x_57);
x_63 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4;
x_64 = l_Lean_Syntax_node3(x_14, x_63, x_45, x_62, x_59);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_43);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_array_fget(x_1, x_8);
lean_dec(x_1);
lean_inc(x_14);
x_67 = l_Lean_Syntax_node3(x_14, x_56, x_66, x_48, x_57);
x_68 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4;
x_69 = l_Lean_Syntax_node3(x_14, x_68, x_45, x_67, x_59);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_43);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_7);
lean_dec(x_4);
x_71 = lean_array_fget(x_1, x_8);
lean_dec(x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_6);
return x_72;
}
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_1);
x_73 = lean_ctor_get(x_4, 5);
lean_inc(x_73);
lean_dec(x_4);
x_74 = 0;
x_75 = l_Lean_SourceInfo_fromRef(x_73, x_74);
x_76 = lean_st_ref_get(x_5, x_6);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5;
lean_inc(x_75);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7;
x_82 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
lean_inc(x_75);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set(x_83, 2, x_82);
x_84 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7;
lean_inc(x_75);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4;
x_87 = l_Lean_Syntax_node3(x_75, x_86, x_80, x_83, x_85);
lean_ctor_set(x_76, 0, x_87);
return x_76;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_dec(x_76);
x_89 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5;
lean_inc(x_75);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7;
x_92 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
lean_inc(x_75);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7;
lean_inc(x_75);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_75);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4;
x_97 = l_Lean_Syntax_node3(x_75, x_96, x_90, x_93, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_88);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_mkTupleSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_mk_syntax_ident(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6;
x_2 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__1;
x_3 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__2;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("num", 3);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("0", 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("1", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_5, x_4, x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_1, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_23);
x_26 = l_instInhabitedNat;
x_27 = l___private_Init_Util_0__outOfBounds___rarg(x_26);
x_28 = lean_box(0);
x_29 = lean_array_get(x_28, x_2, x_27);
lean_dec(x_27);
x_30 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4;
x_31 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = l_Lean_unresolveNameGlobal___at_Lean_Elab_WF_TerminationWF_unexpand___spec__1(x_30, x_31, x_6, x_7, x_8, x_9, x_10);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_mk_syntax_ident(x_33);
x_36 = lean_ctor_get(x_8, 5);
lean_inc(x_36);
x_37 = l_Lean_SourceInfo_fromRef(x_36, x_31);
x_38 = lean_st_ref_get(x_9, x_34);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7;
lean_inc(x_37);
x_41 = l_Lean_Syntax_node1(x_37, x_40, x_29);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__2;
x_43 = l_Lean_Syntax_node2(x_37, x_42, x_35, x_41);
x_16 = x_43;
x_17 = x_39;
goto block_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = lean_array_fget(x_23, x_1);
lean_dec(x_23);
x_45 = lean_box(0);
x_46 = lean_array_get(x_45, x_2, x_44);
lean_dec(x_44);
x_47 = l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4;
x_48 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_unresolveNameGlobal___at_Lean_Elab_WF_TerminationWF_unexpand___spec__1(x_47, x_48, x_6, x_7, x_8, x_9, x_10);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_mk_syntax_ident(x_50);
x_53 = lean_ctor_get(x_8, 5);
lean_inc(x_53);
x_54 = l_Lean_SourceInfo_fromRef(x_53, x_48);
x_55 = lean_st_ref_get(x_9, x_51);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7;
lean_inc(x_54);
x_58 = l_Lean_Syntax_node1(x_54, x_57, x_46);
x_59 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__2;
x_60 = l_Lean_Syntax_node2(x_54, x_59, x_52, x_58);
x_16 = x_60;
x_17 = x_56;
goto block_22;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_13, 0);
lean_inc(x_61);
lean_dec(x_13);
x_62 = lean_nat_dec_eq(x_61, x_1);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_8, 5);
lean_inc(x_63);
x_64 = 0;
x_65 = l_Lean_SourceInfo_fromRef(x_63, x_64);
x_66 = lean_st_ref_get(x_9, x_10);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__5;
lean_inc(x_65);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__4;
x_71 = l_Lean_Syntax_node1(x_65, x_70, x_69);
x_16 = x_71;
x_17 = x_67;
goto block_22;
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_8, 5);
lean_inc(x_72);
x_73 = 0;
x_74 = l_Lean_SourceInfo_fromRef(x_72, x_73);
x_75 = lean_st_ref_get(x_9, x_10);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__6;
lean_inc(x_74);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__4;
x_80 = l_Lean_Syntax_node1(x_74, x_79, x_78);
x_16 = x_80;
x_17 = x_76;
goto block_22;
}
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_array_uset(x_15, x_4, x_16);
x_4 = x_19;
x_5 = x_20;
x_10 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_10, x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_9, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_9, x_22);
lean_dec(x_9);
x_24 = lean_array_fget(x_2, x_10);
x_25 = lean_array_get_size(x_24);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__1(x_26, x_27, x_24);
x_29 = lean_array_get_size(x_3);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
x_31 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2(x_10, x_28, x_30, x_27, x_3, x_13, x_14, x_15, x_16, x_17);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_15);
x_34 = l_Lean_Elab_WF_GuessLex_mkTupleSyntax(x_32, x_13, x_14, x_15, x_16, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_get_size(x_1);
x_38 = lean_nat_dec_lt(x_10, x_37);
lean_dec(x_37);
x_39 = lean_array_get_size(x_28);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__3(x_40, x_27, x_28);
if (x_38 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = l_Lean_instInhabitedName;
x_43 = l___private_Init_Util_0__outOfBounds___rarg(x_42);
x_44 = lean_box(0);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_45);
x_47 = lean_array_push(x_12, x_46);
x_48 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_23;
x_10 = x_48;
x_11 = lean_box(0);
x_12 = x_47;
x_17 = x_36;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_array_fget(x_1, x_10);
x_51 = lean_box(0);
x_52 = 1;
x_53 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_41);
lean_ctor_set(x_53, 3, x_35);
lean_ctor_set_uint8(x_53, sizeof(void*)*4, x_52);
x_54 = lean_array_push(x_12, x_53);
x_55 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_23;
x_10 = x_55;
x_11 = lean_box(0);
x_12 = x_54;
x_17 = x_36;
goto _start;
}
}
else
{
lean_object* x_57; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_12);
lean_ctor_set(x_57, 1, x_17);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_buildTermWF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
lean_inc(x_9);
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__4(x_1, x_2, x_3, x_9, x_12, x_10, x_9, x_11, x_9, x_10, lean_box(0), x_13, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_12);
lean_dec(x_9);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__4___boxed(lean_object** _args) {
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
x_18 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_buildTermWF___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_buildTermWF(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_5);
x_15 = lean_array_get_size(x_9);
x_16 = lean_nat_dec_lt(x_6, x_15);
lean_dec(x_15);
x_17 = lean_nat_dec_lt(x_6, x_4);
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_instInhabitedNat;
x_19 = l___private_Init_Util_0__outOfBounds___rarg(x_18);
if (x_17 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_String_instInhabitedString;
x_21 = l___private_Init_Util_0__outOfBounds___rarg(x_20);
x_22 = lean_string_length(x_21);
lean_dec(x_21);
x_23 = lean_nat_dec_lt(x_19, x_22);
lean_dec(x_19);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
x_24 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_array_set(x_9, x_6, x_22);
x_27 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_27;
x_9 = x_26;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_array_fget(x_3, x_6);
x_30 = lean_string_length(x_29);
lean_dec(x_29);
x_31 = lean_nat_dec_lt(x_19, x_30);
lean_dec(x_19);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
x_32 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_array_set(x_9, x_6, x_30);
x_35 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_35;
x_9 = x_34;
goto _start;
}
}
}
else
{
lean_object* x_37; 
x_37 = lean_array_fget(x_9, x_6);
if (x_17 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = l_String_instInhabitedString;
x_39 = l___private_Init_Util_0__outOfBounds___rarg(x_38);
x_40 = lean_string_length(x_39);
lean_dec(x_39);
x_41 = lean_nat_dec_lt(x_37, x_40);
lean_dec(x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
x_42 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_array_set(x_9, x_6, x_40);
x_45 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_45;
x_9 = x_44;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_array_fget(x_3, x_6);
x_48 = lean_string_length(x_47);
lean_dec(x_47);
x_49 = lean_nat_dec_lt(x_37, x_48);
lean_dec(x_37);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
x_50 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_50;
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_array_set(x_9, x_6, x_48);
x_53 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_53;
x_9 = x_52;
goto _start;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_formatTable___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_uset(x_3, x_2, x_5);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_array_uset(x_6, x_2, x_5);
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_5);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_20 = lean_nat_dec_lt(x_5, x_3);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_2);
x_21 = l___private_Init_Util_0__outOfBounds___rarg(x_2);
x_14 = x_21;
goto block_19;
}
else
{
lean_object* x_22; 
x_22 = lean_array_fget(x_1, x_5);
x_14 = x_22;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_get_size(x_14);
lean_inc(x_15);
x_16 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__1(x_1, x_5, x_14, x_15, x_15, x_10, x_15, x_12, x_8);
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_13;
x_5 = x_17;
x_8 = x_16;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
lean_dec(x_1);
x_11 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1;
x_12 = lean_string_append(x_5, x_11);
x_13 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_13;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = lean_nat_dec_lt(x_6, x_2);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1;
x_10 = lean_string_append(x_3, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_string_append(x_5, x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1(x_2, x_3, x_7, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
x_14 = lean_string_length(x_1);
lean_dec(x_1);
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_15 = l_instInhabitedNat;
x_16 = l___private_Init_Util_0__outOfBounds___rarg(x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_14);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
lean_inc(x_17);
x_19 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4(x_17, x_8, x_17, x_18, x_7);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1(x_2, x_3, x_19, x_20);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_fget(x_4, x_2);
lean_dec(x_4);
x_23 = lean_nat_sub(x_22, x_14);
lean_dec(x_14);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_23);
x_25 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4(x_23, x_8, x_23, x_24, x_7);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1(x_2, x_3, x_25, x_26);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_8, x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_6, x_14);
lean_dec(x_6);
x_16 = lean_nat_dec_lt(x_7, x_5);
x_17 = lean_nat_dec_lt(x_12, x_7);
if (x_16 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_String_instInhabitedString;
x_46 = l___private_Init_Util_0__outOfBounds___rarg(x_45);
x_18 = x_46;
goto block_44;
}
else
{
lean_object* x_47; 
x_47 = lean_array_fget(x_4, x_7);
x_18 = x_47;
goto block_44;
}
block_44:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_box(0);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_7);
x_20 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2(x_18, x_7, x_5, x_2, x_10, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_15;
x_7 = x_22;
x_10 = x_21;
goto _start;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_array_get_size(x_2);
x_25 = lean_nat_dec_lt(x_7, x_24);
lean_dec(x_24);
x_26 = lean_string_length(x_18);
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = l_instInhabitedNat;
x_28 = l___private_Init_Util_0__outOfBounds___rarg(x_27);
x_29 = lean_nat_sub(x_28, x_26);
lean_dec(x_26);
lean_dec(x_28);
lean_inc(x_29);
x_30 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4(x_29, x_12, x_29, x_14, x_10);
lean_dec(x_29);
x_31 = lean_box(0);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_7);
x_32 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2(x_18, x_7, x_5, x_2, x_30, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_15;
x_7 = x_34;
x_10 = x_33;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_array_fget(x_2, x_7);
x_37 = lean_nat_sub(x_36, x_26);
lean_dec(x_26);
lean_dec(x_36);
lean_inc(x_37);
x_38 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4(x_37, x_12, x_37, x_14, x_10);
lean_dec(x_37);
x_39 = lean_box(0);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_7);
x_40 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2(x_18, x_7, x_5, x_2, x_38, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_nat_add(x_7, x_9);
lean_dec(x_7);
x_6 = x_15;
x_7 = x_42;
x_10 = x_41;
goto _start;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_5);
x_15 = lean_nat_dec_lt(x_6, x_3);
x_16 = lean_nat_add(x_6, x_13);
x_17 = lean_nat_dec_lt(x_16, x_3);
lean_dec(x_16);
if (x_15 == 0)
{
lean_object* x_28; 
lean_inc(x_2);
x_28 = l___private_Init_Util_0__outOfBounds___rarg(x_2);
x_18 = x_28;
goto block_27;
}
else
{
lean_object* x_29; 
x_29 = lean_array_fget(x_1, x_6);
x_18 = x_29;
goto block_27;
}
block_27:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_get_size(x_18);
lean_inc_n(x_19, 2);
lean_inc(x_4);
x_20 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5(x_1, x_4, x_6, x_18, x_19, x_19, x_11, x_19, x_13, x_9);
lean_dec(x_19);
lean_dec(x_18);
if (x_17 == 0)
{
lean_object* x_21; 
x_21 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_21;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___closed__1;
x_24 = lean_string_append(x_20, x_23);
x_25 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_25;
x_9 = x_24;
goto _start;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_formatTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; size_t x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
x_5 = 0;
if (x_4 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_17 = l___private_Init_Util_0__outOfBounds___rarg(x_16);
x_6 = x_17;
goto block_15;
}
else
{
lean_object* x_18; 
x_18 = lean_array_fget(x_1, x_3);
x_6 = x_18;
goto block_15;
}
block_15:
{
lean_object* x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_formatTable___spec__2(x_8, x_5, x_6);
x_10 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_2);
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__3(x_1, x_10, x_2, x_2, x_3, x_2, x_11, x_9);
x_13 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
lean_inc(x_2);
x_14 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6(x_1, x_10, x_2, x_12, x_2, x_3, x_2, x_11, x_13);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_formatTable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_formatTable___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_formatTable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_WF_GuessLex_formatTable(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = 0;
x_10 = l_Lean_Syntax_getPos_x3f(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_11 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_FileMap_toPosition(x_7, x_13);
lean_dec(x_13);
x_15 = l_Lean_Syntax_getTailPos_x3f(x_8, x_9);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_inc(x_16);
x_17 = l_Nat_repr(x_16);
x_18 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Nat_repr(x_22);
x_24 = lean_string_append(x_21, x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_24, x_18);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_26 = lean_string_append(x_25, x_18);
x_27 = lean_string_append(x_26, x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = l_Lean_FileMap_toPosition(x_7, x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_nat_dec_eq(x_31, x_16);
lean_dec(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = l_Nat_repr(x_31);
x_34 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__2;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = lean_string_append(x_35, x_20);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = l_Nat_repr(x_37);
x_39 = lean_string_append(x_36, x_38);
lean_dec(x_38);
x_40 = lean_string_append(x_39, x_18);
x_41 = lean_string_append(x_25, x_40);
lean_dec(x_40);
x_42 = lean_string_append(x_41, x_18);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_31);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_45 = l_Nat_repr(x_44);
x_46 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__2;
x_47 = lean_string_append(x_46, x_45);
lean_dec(x_45);
x_48 = lean_string_append(x_47, x_18);
x_49 = lean_string_append(x_25, x_48);
lean_dec(x_48);
x_50 = lean_string_append(x_49, x_18);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_erase_macro_scopes(x_5);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry(x_1, x_3, x_3, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_push(x_6, x_18);
x_21 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_21;
x_6 = x_20;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(") ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_27 = lean_ctor_get(x_19, 2);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_30 = lean_array_fget(x_21, x_22);
x_31 = lean_nat_add(x_22, x_16);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString(x_32, x_8, x_9, x_10, x_11, x_12);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_nat_add(x_4, x_16);
x_37 = l_Nat_repr(x_36);
x_38 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_39 = lean_string_append(x_38, x_37);
lean_dec(x_37);
x_40 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_34);
lean_dec(x_34);
x_43 = lean_string_append(x_42, x_38);
lean_inc(x_2);
x_44 = lean_array_push(x_2, x_43);
lean_inc(x_1);
x_45 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2(x_30, x_1, x_14, x_1, x_16, x_44, x_8, x_9, x_10, x_11, x_35);
lean_dec(x_30);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_push(x_20, x_46);
lean_ctor_set(x_7, 1, x_48);
x_49 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_49;
x_12 = x_47;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_19);
x_51 = lean_array_fget(x_21, x_22);
x_52 = lean_nat_add(x_22, x_16);
lean_dec(x_22);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_23);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
x_55 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString(x_54, x_8, x_9, x_10, x_11, x_12);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_nat_add(x_4, x_16);
x_59 = l_Nat_repr(x_58);
x_60 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_61 = lean_string_append(x_60, x_59);
lean_dec(x_59);
x_62 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_string_append(x_63, x_56);
lean_dec(x_56);
x_65 = lean_string_append(x_64, x_60);
lean_inc(x_2);
x_66 = lean_array_push(x_2, x_65);
lean_inc(x_1);
x_67 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2(x_51, x_1, x_14, x_1, x_16, x_66, x_8, x_9, x_10, x_11, x_57);
lean_dec(x_51);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_array_push(x_20, x_68);
lean_ctor_set(x_7, 1, x_70);
lean_ctor_set(x_7, 0, x_53);
x_71 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_71;
x_12 = x_69;
goto _start;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_7, 0);
x_74 = lean_ctor_get(x_7, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_7);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 2);
lean_inc(x_77);
x_78 = lean_nat_dec_lt(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_74);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_12);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
x_82 = lean_array_fget(x_75, x_76);
x_83 = lean_nat_add(x_76, x_16);
lean_dec(x_76);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 3, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_77);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
x_86 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString(x_85, x_8, x_9, x_10, x_11, x_12);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_nat_add(x_4, x_16);
x_90 = l_Nat_repr(x_89);
x_91 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_string_append(x_94, x_87);
lean_dec(x_87);
x_96 = lean_string_append(x_95, x_91);
lean_inc(x_2);
x_97 = lean_array_push(x_2, x_96);
lean_inc(x_1);
x_98 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2(x_82, x_1, x_14, x_1, x_16, x_97, x_8, x_9, x_10, x_11, x_88);
lean_dec(x_82);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_array_push(x_74, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_84);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_103;
x_7 = x_102;
x_12 = x_100;
goto _start;
}
}
}
else
{
lean_object* x_105; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_7);
lean_ctor_set(x_105, 1, x_12);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_7);
lean_ctor_set(x_106, 1, x_12);
return x_106;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
x_2 = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainNonMutualFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__1(x_9, x_10, x_1);
x_12 = l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___closed__1;
x_13 = l_Array_append___rarg(x_12, x_11);
x_14 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_array_get_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
x_18 = l_Array_toSubarray___rarg(x_2, x_17, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_16);
x_21 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3(x_8, x_14, x_16, x_17, x_16, x_20, x_19, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_WF_GuessLex_formatTable(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_WF_GuessLex_formatTable(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_GuessLex_explainNonMutualFailure(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_18 = l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry(x_1, x_4, x_2, x_8, x_9, x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_push(x_7, x_19);
x_22 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_22;
x_7 = x_21;
x_12 = x_20;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_18 = l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry(x_1, x_4, x_2, x_8, x_9, x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_push(x_7, x_19);
x_22 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_22;
x_7 = x_21;
x_12 = x_20;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_dec_lt(x_6, x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = l_Lean_instInhabitedName;
x_22 = l___private_Init_Util_0__outOfBounds___rarg(x_21);
x_23 = lean_erase_macro_scopes(x_22);
x_24 = 1;
x_25 = l_Lean_Name_toString(x_23, x_24);
x_26 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_27 = lean_array_push(x_26, x_25);
lean_inc(x_2);
x_28 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__1(x_1, x_6, x_2, x_16, x_2, x_18, x_27, x_10, x_11, x_12, x_13, x_14);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_array_push(x_9, x_29);
x_32 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_32;
x_9 = x_31;
x_14 = x_30;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_array_fget(x_3, x_6);
x_35 = lean_erase_macro_scopes(x_34);
x_36 = 1;
x_37 = l_Lean_Name_toString(x_35, x_36);
x_38 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_39 = lean_array_push(x_38, x_37);
lean_inc(x_2);
x_40 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__2(x_1, x_6, x_2, x_16, x_2, x_18, x_39, x_10, x_11, x_12, x_13, x_14);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_array_push(x_9, x_41);
x_44 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_44;
x_9 = x_43;
x_14 = x_42;
goto _start;
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_14);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_9);
lean_ctor_set(x_47, 1, x_14);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
x_17 = l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry(x_1, x_3, x_3, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_push(x_6, x_18);
x_21 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_21;
x_6 = x_20;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_Elab_WF_GuessLex_formatTable(x_2);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___closed__1;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Call from ", 10);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" to ", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("at ", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":\n", 2);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString(x_15, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_1);
x_22 = lean_nat_dec_lt(x_16, x_21);
x_23 = lean_nat_dec_lt(x_17, x_21);
lean_dec(x_21);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__7;
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__9;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_get_size(x_2);
x_30 = lean_nat_dec_lt(x_16, x_29);
x_31 = 0;
x_32 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__10;
x_33 = lean_nat_dec_eq(x_16, x_17);
if (x_22 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_instInhabitedName;
x_122 = l___private_Init_Util_0__outOfBounds___rarg(x_121);
x_34 = x_122;
goto block_120;
}
else
{
lean_object* x_123; 
x_123 = lean_array_fget(x_1, x_16);
x_34 = x_123;
goto block_120;
}
block_120:
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = 1;
x_36 = l_Lean_Name_toString(x_34, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__2;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__4;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
if (x_23 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = l_Lean_instInhabitedName;
x_118 = l___private_Init_Util_0__outOfBounds___rarg(x_117);
x_42 = x_118;
goto block_116;
}
else
{
lean_object* x_119; 
x_119 = lean_array_fget(x_1, x_17);
x_42 = x_119;
goto block_116;
}
block_116:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = l_Lean_Name_toString(x_42, x_35);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__5;
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_28);
if (x_30 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_16);
x_113 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_114 = l___private_Init_Util_0__outOfBounds___rarg(x_113);
x_50 = x_114;
goto block_112;
}
else
{
lean_object* x_115; 
x_115 = lean_array_fget(x_2, x_16);
lean_dec(x_16);
x_50 = x_115;
goto block_112;
}
block_112:
{
lean_object* x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_array_get_size(x_50);
x_52 = lean_usize_of_nat(x_51);
x_53 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__1(x_52, x_31, x_50);
x_54 = l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___closed__1;
x_55 = l_Array_append___rarg(x_54, x_53);
x_56 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
x_57 = lean_array_push(x_56, x_55);
if (x_33 == 0)
{
uint8_t x_84; 
x_84 = lean_nat_dec_lt(x_17, x_29);
lean_dec(x_29);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_17);
x_85 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_86 = l___private_Init_Util_0__outOfBounds___rarg(x_85);
x_58 = x_86;
goto block_83;
}
else
{
lean_object* x_87; 
x_87 = lean_array_fget(x_2, x_17);
lean_dec(x_17);
x_58 = x_87;
goto block_83;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_29);
lean_dec(x_17);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_unsigned_to_nat(1u);
lean_inc(x_51);
x_90 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__4(x_14, x_51, x_88, x_51, x_89, x_54, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_51);
lean_dec(x_14);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_array_push(x_57, x_91);
x_94 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_95 = lean_apply_8(x_32, x_49, x_93, x_94, x_7, x_8, x_9, x_10, x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
lean_dec(x_96);
lean_ctor_set(x_95, 0, x_99);
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
lean_dec(x_96);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; 
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
lean_dec(x_95);
x_104 = lean_ctor_get(x_96, 0);
lean_inc(x_104);
lean_dec(x_96);
x_105 = 1;
x_106 = lean_usize_add(x_5, x_105);
x_5 = x_106;
x_6 = x_104;
x_11 = x_103;
goto _start;
}
}
else
{
uint8_t x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_108 = !lean_is_exclusive(x_95);
if (x_108 == 0)
{
return x_95;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_95, 0);
x_110 = lean_ctor_get(x_95, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_95);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
block_83:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_array_get_size(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_unsigned_to_nat(1u);
lean_inc(x_59);
x_62 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__3(x_14, x_51, x_58, x_59, x_59, x_60, x_59, x_61, x_57, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_14);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_66 = lean_apply_8(x_32, x_49, x_63, x_65, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
x_76 = 1;
x_77 = lean_usize_add(x_5, x_76);
x_5 = x_77;
x_6 = x_75;
x_11 = x_74;
goto _start;
}
}
else
{
uint8_t x_79; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
return x_66;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_66, 0);
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_66);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainMutualFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5(x_1, x_2, x_3, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
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
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainMutualFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_explainMutualFailure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("The arguments relate at each recursive call as follows:\n", 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(<, ≤, =: relation proved, \? all proofs failed, _: no proof attempted)\n", 73);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__2;
x_2 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__4;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_explainFailure___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__6;
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_WF_GuessLex_explainMutualFailure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__5;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_box(0);
x_19 = lean_apply_7(x_9, x_17, x_18, x_4, x_5, x_6, x_7, x_15);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get_size(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_28 = l___private_Init_Util_0__outOfBounds___rarg(x_27);
x_29 = l_Lean_Elab_WF_GuessLex_explainNonMutualFailure(x_28, x_3, x_4, x_5, x_6, x_7, x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__5;
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
x_34 = lean_box(0);
x_35 = lean_apply_7(x_9, x_33, x_34, x_4, x_5, x_6, x_7, x_31);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_array_fget(x_2, x_25);
x_37 = l_Lean_Elab_WF_GuessLex_explainNonMutualFailure(x_36, x_3, x_4, x_5, x_6, x_7, x_8);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_WF_GuessLex_explainFailure___closed__5;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_box(0);
x_43 = lean_apply_7(x_9, x_41, x_42, x_4, x_5, x_6, x_7, x_39);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_GuessLex_explainFailure___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_explainFailure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_explainFailure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_Lean_Elab_WF_GuessLex_naryVarNames(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_14, x_3, x_16);
x_3 = x_19;
x_4 = x_20;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_array_get_size(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_Lean_Elab_WF_GuessLex_getForbiddenByTrivialSizeOf(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_14, x_3, x_16);
x_3 = x_19;
x_4 = x_20;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_1);
x_15 = l_Lean_Elab_WF_GuessLex_RecCallCache_mk(x_1, x_12, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_14, x_3, x_16);
x_3 = x_19;
x_4 = x_20;
x_9 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_WF_GuessLex_inspectCall), 7, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_guessLex___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = lean_apply_6(x_20, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = 0;
x_26 = lean_unbox(x_23);
x_27 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_28 = lean_array_push(x_19, x_13);
x_29 = 2;
x_30 = lean_unbox(x_23);
x_31 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_30, x_29);
if (x_31 == 0)
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; 
x_32 = 1;
x_33 = lean_unbox(x_23);
lean_dec(x_23);
x_34 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_33, x_32);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_15, 1, x_28);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_5, 0, x_36);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
size_t x_37; size_t x_38; 
lean_free_object(x_21);
lean_ctor_set(x_15, 1, x_28);
x_37 = 1;
x_38 = lean_usize_add(x_4, x_37);
x_4 = x_38;
x_10 = x_24;
goto _start;
}
}
else
{
size_t x_40; size_t x_41; 
lean_free_object(x_21);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_28);
x_40 = 1;
x_41 = lean_usize_add(x_4, x_40);
x_4 = x_41;
x_10 = x_24;
goto _start;
}
}
else
{
uint8_t x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_13);
x_43 = 1;
x_44 = lean_box(x_43);
lean_ctor_set(x_15, 0, x_44);
x_45 = 1;
x_46 = lean_usize_add(x_4, x_45);
x_4 = x_46;
x_10 = x_24;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = 0;
x_51 = lean_unbox(x_48);
x_52 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_51, x_50);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; 
x_53 = lean_array_push(x_19, x_13);
x_54 = 2;
x_55 = lean_unbox(x_48);
x_56 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_55, x_54);
if (x_56 == 0)
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; 
x_57 = 1;
x_58 = lean_unbox(x_48);
lean_dec(x_48);
x_59 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_58, x_57);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_15, 1, x_53);
x_60 = 0;
x_61 = lean_box(x_60);
lean_ctor_set(x_5, 0, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_49);
return x_62;
}
else
{
size_t x_63; size_t x_64; 
lean_ctor_set(x_15, 1, x_53);
x_63 = 1;
x_64 = lean_usize_add(x_4, x_63);
x_4 = x_64;
x_10 = x_49;
goto _start;
}
}
else
{
size_t x_66; size_t x_67; 
lean_dec(x_48);
lean_ctor_set(x_15, 1, x_53);
x_66 = 1;
x_67 = lean_usize_add(x_4, x_66);
x_4 = x_67;
x_10 = x_49;
goto _start;
}
}
else
{
uint8_t x_69; lean_object* x_70; size_t x_71; size_t x_72; 
lean_dec(x_48);
lean_dec(x_18);
lean_dec(x_13);
x_69 = 1;
x_70 = lean_box(x_69);
lean_ctor_set(x_15, 0, x_70);
x_71 = 1;
x_72 = lean_usize_add(x_4, x_71);
x_4 = x_72;
x_10 = x_49;
goto _start;
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_21);
if (x_74 == 0)
{
return x_21;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_21, 0);
x_76 = lean_ctor_get(x_21, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_21);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_5, 0);
x_79 = lean_ctor_get(x_15, 0);
x_80 = lean_ctor_get(x_15, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_15);
x_81 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_82 = lean_apply_6(x_81, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = 0;
x_87 = lean_unbox(x_83);
x_88 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_87, x_86);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; 
x_89 = lean_array_push(x_80, x_13);
x_90 = 2;
x_91 = lean_unbox(x_83);
x_92 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_91, x_90);
if (x_92 == 0)
{
uint8_t x_93; uint8_t x_94; uint8_t x_95; 
x_93 = 1;
x_94 = lean_unbox(x_83);
lean_dec(x_83);
x_95 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_94, x_93);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_78);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_79);
lean_ctor_set(x_96, 1, x_89);
x_97 = 0;
x_98 = lean_box(x_97);
lean_ctor_set(x_5, 1, x_96);
lean_ctor_set(x_5, 0, x_98);
if (lean_is_scalar(x_85)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_85;
}
lean_ctor_set(x_99, 0, x_5);
lean_ctor_set(x_99, 1, x_84);
return x_99;
}
else
{
lean_object* x_100; size_t x_101; size_t x_102; 
lean_dec(x_85);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_79);
lean_ctor_set(x_100, 1, x_89);
lean_ctor_set(x_5, 1, x_100);
x_101 = 1;
x_102 = lean_usize_add(x_4, x_101);
x_4 = x_102;
x_10 = x_84;
goto _start;
}
}
else
{
lean_object* x_104; size_t x_105; size_t x_106; 
lean_dec(x_85);
lean_dec(x_83);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_79);
lean_ctor_set(x_104, 1, x_89);
lean_ctor_set(x_5, 1, x_104);
x_105 = 1;
x_106 = lean_usize_add(x_4, x_105);
x_4 = x_106;
x_10 = x_84;
goto _start;
}
}
else
{
uint8_t x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_13);
x_108 = 1;
x_109 = lean_box(x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_80);
lean_ctor_set(x_5, 1, x_110);
x_111 = 1;
x_112 = lean_usize_add(x_4, x_111);
x_4 = x_112;
x_10 = x_84;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_80);
lean_dec(x_79);
lean_free_object(x_5);
lean_dec(x_78);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_114 = lean_ctor_get(x_82, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_82, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_116 = x_82;
} else {
 lean_dec_ref(x_82);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_5, 1);
x_119 = lean_ctor_get(x_5, 0);
lean_inc(x_118);
lean_inc(x_119);
lean_dec(x_5);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_array_uget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_124 = lean_apply_6(x_123, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = 0;
x_129 = lean_unbox(x_125);
x_130 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_129, x_128);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; 
x_131 = lean_array_push(x_121, x_13);
x_132 = 2;
x_133 = lean_unbox(x_125);
x_134 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_133, x_132);
if (x_134 == 0)
{
uint8_t x_135; uint8_t x_136; uint8_t x_137; 
x_135 = 1;
x_136 = lean_unbox(x_125);
lean_dec(x_125);
x_137 = l_Lean_Elab_WF_GuessLex_instDecidableEqGuessLexRel(x_136, x_135);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_119);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_122)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_122;
}
lean_ctor_set(x_138, 0, x_120);
lean_ctor_set(x_138, 1, x_131);
x_139 = 0;
x_140 = lean_box(x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
if (lean_is_scalar(x_127)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_127;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_126);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; size_t x_145; size_t x_146; 
lean_dec(x_127);
if (lean_is_scalar(x_122)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_122;
}
lean_ctor_set(x_143, 0, x_120);
lean_ctor_set(x_143, 1, x_131);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_119);
lean_ctor_set(x_144, 1, x_143);
x_145 = 1;
x_146 = lean_usize_add(x_4, x_145);
x_4 = x_146;
x_5 = x_144;
x_10 = x_126;
goto _start;
}
}
else
{
lean_object* x_148; lean_object* x_149; size_t x_150; size_t x_151; 
lean_dec(x_127);
lean_dec(x_125);
if (lean_is_scalar(x_122)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_122;
}
lean_ctor_set(x_148, 0, x_120);
lean_ctor_set(x_148, 1, x_131);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_119);
lean_ctor_set(x_149, 1, x_148);
x_150 = 1;
x_151 = lean_usize_add(x_4, x_150);
x_4 = x_151;
x_5 = x_149;
x_10 = x_126;
goto _start;
}
}
else
{
uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; size_t x_157; size_t x_158; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_13);
x_153 = 1;
x_154 = lean_box(x_153);
if (lean_is_scalar(x_122)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_122;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_121);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_119);
lean_ctor_set(x_156, 1, x_155);
x_157 = 1;
x_158 = lean_usize_add(x_4, x_157);
x_4 = x_158;
x_5 = x_156;
x_10 = x_126;
goto _start;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_160 = lean_ctor_get(x_124, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_124, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_162 = x_124;
} else {
 lean_dec_ref(x_124);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Array_eraseIdx___rarg(x_1, x_2);
x_13 = lean_array_push(x_3, x_4);
x_14 = l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7(x_12, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_nat_dec_lt(x_11, x_8);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_10, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_10, x_23);
lean_dec(x_10);
x_25 = lean_array_fget(x_1, x_11);
x_26 = lean_array_get_size(x_2);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__2;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_25);
x_30 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_guessLex___spec__8(x_25, x_2, x_27, x_28, x_29, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_25);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_nat_add(x_11, x_9);
lean_dec(x_11);
lean_inc(x_6);
{
lean_object* _tmp_9 = x_24;
lean_object* _tmp_10 = x_36;
lean_object* _tmp_11 = lean_box(0);
lean_object* _tmp_12 = x_6;
lean_object* _tmp_17 = x_35;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_12 = _tmp_11;
x_13 = _tmp_12;
x_18 = _tmp_17;
}
goto _start;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
lean_dec(x_31);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_25);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_nat_add(x_11, x_9);
lean_dec(x_11);
lean_inc(x_6);
{
lean_object* _tmp_9 = x_24;
lean_object* _tmp_10 = x_41;
lean_object* _tmp_11 = lean_box(0);
lean_object* _tmp_12 = x_6;
lean_object* _tmp_17 = x_40;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_12 = _tmp_11;
x_13 = _tmp_12;
x_18 = _tmp_17;
}
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_3);
lean_inc(x_1);
x_46 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___lambda__1(x_1, x_11, x_3, x_25, x_44, x_45, x_14, x_15, x_16, x_17, x_43);
lean_dec(x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_nat_add(x_11, x_9);
lean_dec(x_11);
x_10 = x_24;
x_11 = x_56;
x_12 = lean_box(0);
x_13 = x_55;
x_18 = x_54;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_30);
if (x_62 == 0)
{
return x_30;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_30, 0);
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_30);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_13);
lean_ctor_set(x_66, 1, x_18);
return x_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4;
lean_inc(x_10);
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9(x_1, x_2, x_3, x_10, x_13, x_15, x_11, x_10, x_12, x_10, x_11, lean_box(0), x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
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
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
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
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___lambda__1(x_1, x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve___at_Lean_Elab_WF_guessLex___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1;
x_9 = l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_guessLex___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_guessLex___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Elab_addAsAxiom(x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutModifyingState___at_Lean_Elab_WF_guessLex___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_WF_guessLex___spec__14(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_to_list(lean_box(0), x_5);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at_Lean_Meta_substCore___spec__6(x_7, x_8);
x_10 = l_Lean_MessageData_ofList(x_9);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_array_to_list(lean_box(0), x_12);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at_Lean_Meta_substCore___spec__6(x_14, x_15);
x_17 = l_Lean_MessageData_ofList(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_13;
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Elab_WF_TerminationWF_unexpand(x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_3, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Elab_WF_TerminationWF_unexpand(x_2, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_guessLex___spec__12(x_4, x_5, x_6, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_WF_TerminationWF_unexpand(x_2, x_7, x_8, x_9, x_10, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Could not find a decreasing measure.\n", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_guessLex___lambda__2___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_guessLex___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Please use `termination_by` to specify a decreasing measure.", 60);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_guessLex___lambda__2___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_guessLex___lambda__2___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_WF_GuessLex_showInferredTerminationBy;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Inferred termination argument:", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_guessLex___lambda__2___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = l_Lean_Elab_WF_GuessLex_collectRecCalls(x_1, x_2, x_3, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_WF_GuessLex_filterSubsumed___closed__1;
x_21 = l_Array_filterPairsM___at_Lean_Elab_WF_GuessLex_filterSubsumed___spec__3___rarg(x_18, x_20);
lean_dec(x_18);
x_22 = lean_array_get_size(x_21);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4(x_4, x_23, x_5, x_21, x_12, x_13, x_14, x_15, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_25);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc(x_25);
x_29 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__5(x_28, x_5, x_25);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_30 = l_Lean_Elab_WF_GuessLex_solve___at_Lean_Elab_WF_guessLex___spec__6(x_6, x_29, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_10);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10(x_7, x_5, x_8);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_34 = l_Lean_Elab_WF_GuessLex_explainFailure(x_33, x_9, x_25, x_12, x_13, x_14, x_15, x_32);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_35);
x_38 = l_Lean_Elab_WF_guessLex___lambda__2___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_WF_guessLex___lambda__2___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_WF_guessLex___lambda__2___closed__7;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at_Lean_Elab_WF_guessLex___spec__11(x_43, x_12, x_13, x_14, x_15, x_36);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_25);
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
lean_dec(x_31);
lean_inc(x_8);
x_51 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10(x_7, x_5, x_8);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_52 = l_Lean_Elab_WF_GuessLex_buildTermWF(x_51, x_9, x_50, x_12, x_13, x_14, x_15, x_49);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_lt(x_55, x_10);
x_57 = lean_box(x_56);
x_58 = lean_box_usize(x_5);
x_59 = lean_box_usize(x_7);
lean_inc(x_53);
x_60 = lean_alloc_closure((void*)(l_Lean_Elab_WF_guessLex___lambda__1___boxed), 11, 6);
lean_closure_set(x_60, 0, x_57);
lean_closure_set(x_60, 1, x_53);
lean_closure_set(x_60, 2, x_10);
lean_closure_set(x_60, 3, x_8);
lean_closure_set(x_60, 4, x_58);
lean_closure_set(x_60, 5, x_59);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_61 = l_Lean_withoutModifyingState___at_Lean_Elab_WF_guessLex___spec__13(x_60, x_12, x_13, x_14, x_15, x_54);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = lean_ctor_get(x_14, 2);
lean_inc(x_65);
x_66 = l_Lean_Elab_WF_guessLex___lambda__2___closed__8;
x_67 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_dec(x_63);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_ctor_set(x_61, 0, x_53);
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
lean_free_object(x_61);
x_68 = l_Lean_MessageData_ofSyntax(x_63);
x_69 = l_Lean_Elab_WF_guessLex___lambda__2___closed__10;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = 0;
x_74 = l_Lean_log___at_Lean_Meta_computeSynthOrder___spec__6(x_72, x_73, x_12, x_13, x_14, x_15, x_64);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_53);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_53);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_61, 0);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_61);
x_81 = lean_ctor_get(x_14, 2);
lean_inc(x_81);
x_82 = l_Lean_Elab_WF_guessLex___lambda__2___closed__8;
x_83 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_81, x_82);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_79);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_53);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = l_Lean_MessageData_ofSyntax(x_79);
x_86 = l_Lean_Elab_WF_guessLex___lambda__2___closed__10;
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = 0;
x_91 = l_Lean_log___at_Lean_Meta_computeSynthOrder___spec__6(x_89, x_90, x_12, x_13, x_14, x_15, x_80);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_53);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_53);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_95 = !lean_is_exclusive(x_61);
if (x_95 == 0)
{
return x_61;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_61, 0);
x_97 = lean_ctor_get(x_61, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_61);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_99 = !lean_is_exclusive(x_30);
if (x_99 == 0)
{
return x_30;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_30, 0);
x_101 = lean_ctor_get(x_30, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_30);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_103 = !lean_is_exclusive(x_17);
if (x_103 == 0)
{
return x_17;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_17, 0);
x_105 = lean_ctor_get(x_17, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_17);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_dec(x_10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__3(x_1, x_2, x_3, x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_5);
x_19 = l_Lean_Elab_WF_GuessLex_generateMeasures(x_17, x_5, x_11, x_12, x_13, x_14, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_array_get_size(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_WF_guessLex___lambda__2(x_6, x_1, x_5, x_7, x_3, x_20, x_2, x_4, x_8, x_9, x_25, x_11, x_12, x_13, x_14, x_21);
lean_dec(x_8);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_fget(x_20, x_27);
lean_dec(x_20);
x_29 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10(x_2, x_3, x_4);
x_30 = l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20;
x_31 = lean_array_push(x_30, x_28);
x_32 = l_Lean_Elab_WF_GuessLex_buildTermWF(x_29, x_8, x_31, x_11, x_12, x_13, x_14, x_21);
lean_dec(x_8);
lean_dec(x_29);
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
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
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
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("varNames is: ", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_guessLex___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_guessLex___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__1(x_3, x_11, x_12, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
lean_inc(x_14);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__2(x_17, x_12, x_14);
x_19 = l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3;
x_20 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_19, x_5, x_6, x_7, x_8, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_WF_guessLex___lambda__3(x_3, x_11, x_12, x_1, x_18, x_2, x_4, x_14, x_10, x_24, x_5, x_6, x_7, x_8, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
lean_inc(x_14);
x_27 = lean_array_to_list(lean_box(0), x_14);
x_28 = lean_box(0);
x_29 = l_List_mapTR_loop___at_Lean_Elab_WF_guessLex___spec__14(x_27, x_28);
x_30 = l_Lean_MessageData_ofList(x_29);
lean_dec(x_29);
x_31 = l_Lean_Elab_WF_guessLex___closed__2;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_19, x_34, x_5, x_6, x_7, x_8, x_26);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_WF_guessLex___lambda__3(x_3, x_11, x_12, x_1, x_18, x_2, x_4, x_14, x_10, x_36, x_5, x_6, x_7, x_8, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_13);
if (x_39 == 0)
{
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_guessLex___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_guessLex___spec__8(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_guessLex___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_GuessLex_solve_go___at_Lean_Elab_WF_guessLex___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_GuessLex_solve___at_Lean_Elab_WF_guessLex___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_WF_GuessLex_solve___at_Lean_Elab_WF_guessLex___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_guessLex___spec__10(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_guessLex___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_WF_guessLex___spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_guessLex___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_guessLex___spec__12(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Lean_Elab_WF_guessLex___lambda__1(x_12, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Lean_Elab_WF_guessLex___lambda__2(x_1, x_2, x_3, x_4, x_17, x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_guessLex___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_17 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_18 = l_Lean_Elab_WF_guessLex___lambda__3(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_HasConstCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CasesOn(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cleanup(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Quotation(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_RecAppSyntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_TerminationHint(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Array(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_HasConstCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CasesOn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cleanup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_RecAppSyntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Array(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__1 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__1);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__2 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__2);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__3);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__4 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__4);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__5 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__5);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__6);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__7 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__7();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__7);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__8 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__8();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__8);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__9 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__9();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__9);
l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__10 = _init_l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__10();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9____closed__10);
if (builtin) {res = l_Lean_Elab_WF_GuessLex_initFn____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_9_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_WF_GuessLex_showInferredTerminationBy = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_showInferredTerminationBy);
lean_dec_ref(res);
}l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1 = _init_l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_naryVarNames_freshen___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_naryVarNames___spec__1___closed__1);
l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1 = _init_l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_naryVarNames___lambda__1___closed__1);
l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1 = _init_l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_withRecApps_processRec___rarg___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__3);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__4 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__4);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_WF_GuessLex_withRecApps_loop___spec__5___rarg___lambda__2___closed__5);
l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_withRecApps___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__1 = _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__1);
l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__2 = _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__2);
l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3 = _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__3);
l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__4 = _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__4);
l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__5 = _init_l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_withRecApps___rarg___closed__5);
l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___closed__1 = _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__1___closed__1);
l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__1 = _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__1);
l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2 = _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__2);
l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__3 = _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__3);
l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__4 = _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_filterSubsumed___lambda__2___closed__4);
l_Lean_Elab_WF_GuessLex_filterSubsumed___closed__1 = _init_l_Lean_Elab_WF_GuessLex_filterSubsumed___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_filterSubsumed___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__2 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__2);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__3 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__3);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__4 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__4();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__4);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__5 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__5();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__5);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__6 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__6();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__6);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__7 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__7();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__3___closed__7);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__2 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__2);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__3 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__3);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__4 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__4();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__4);
l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__5 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__5();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_WF_GuessLex_collectRecCalls___spec__5___closed__5);
l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__1 = _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__1);
l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__2 = _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__2___closed__2);
l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__1 = _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__1);
l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__2 = _init_l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_collectRecCalls___lambda__4___closed__2);
l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___closed__1 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_noConfusion___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__1);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__2);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__3);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__4);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__5);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__6);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__7);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__8);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__9);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__10);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__11);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__12 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__12);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__13 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__13);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__14 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__14);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__15 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__15);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__16 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__16);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__17 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__17);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__18 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__18();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__18);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__19 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__19();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__19);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__20 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__20();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__20);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__21 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__21();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__21);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__22 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__22();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__22);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__23 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__23();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__23);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__24 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__24();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__24);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__25 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__25();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__25);
l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__26 = _init_l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__26();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_GuessLex_0__Lean_Elab_WF_GuessLex_reprGuessLexRel____x40_Lean_Elab_PreDefinition_WF_GuessLex___hyg_2322____closed__26);
l_Lean_Elab_WF_GuessLex_instReprGuessLexRel___closed__1 = _init_l_Lean_Elab_WF_GuessLex_instReprGuessLexRel___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instReprGuessLexRel___closed__1);
l_Lean_Elab_WF_GuessLex_instReprGuessLexRel = _init_l_Lean_Elab_WF_GuessLex_instReprGuessLexRel();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instReprGuessLexRel);
l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1 = _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__1);
l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2 = _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__2);
l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3 = _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__3);
l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4 = _init_l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToStringGuessLexRel___closed__4);
l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1 = _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__1);
l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2 = _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__2);
l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3 = _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__3);
l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4 = _init_l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_instToFormatGuessLexRel___closed__4);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__1 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__1);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__2 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__2);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__3 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__3);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__4 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__4);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__5 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__5);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__6 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__6);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__7 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__7);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__8 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__8);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__9 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__9();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__9);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__10 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__10();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__10);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__11 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__11();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__11);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__12 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__12();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__12);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__13 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__13();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__13);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__14 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__14();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__14);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__15 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__15();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__15);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__16 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__16();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__16);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__17 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__17();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__17);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__18 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__18();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__18);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__19 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__19();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__19);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__20);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__21 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__21();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__21);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__22 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__22();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__22);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__23 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__23();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__23);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__24 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__24();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__24);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__25 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__25();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__25);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__26 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__26();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__26);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__27 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__27();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__27);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__28 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__28();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__28);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__29 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__29();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__29);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__30 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__30();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__30);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__31 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__31();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__31);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__32 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__32();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__32);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__33 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__33();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__33);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__34 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__34();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__34);
l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__35 = _init_l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__35();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_GuessLexRel_toNatRel___closed__35);
l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__1 = _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__1);
l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__2 = _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__2);
l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__3 = _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__3);
l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4 = _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__4);
l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__5 = _init_l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkSizeOf___closed__5);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__1);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__2___closed__2);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__3___closed__1);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__1);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__2);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__5___closed__3);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__1);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__2);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__3);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__4 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__4);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__5 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__5();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__5);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__6 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__6();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__6);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__7 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__7();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__7);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__8 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__8();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__8);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__9 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__9();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__9);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__10 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__10();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__10);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__11 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__11();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__11);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__12 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__12();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___lambda__8___closed__12);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__1);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__2);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__3);
l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__4 = _init_l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_WF_GuessLex_evalRecCall___spec__3___closed__4);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__1 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__1);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__2 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__2);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__3 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__3);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__4);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__5 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__2___closed__5);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__1 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__1);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__2 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__2);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__3 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__3);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__4 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__4);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__5 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__5);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__6 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__6);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__7);
l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__8 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___lambda__3___closed__8);
l_Lean_Elab_WF_GuessLex_evalRecCall___closed__1 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___closed__1);
l_Lean_Elab_WF_GuessLex_evalRecCall___closed__2 = _init_l_Lean_Elab_WF_GuessLex_evalRecCall___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_evalRecCall___closed__2);
l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___closed__1 = _init_l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_RecCallCache_prettyEntry___closed__1);
l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1 = _init_l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_generateCombinations_x3f_goUniform___closed__1);
l_Lean_Elab_WF_GuessLex_generateMeasures___closed__1 = _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_generateMeasures___closed__1);
l_Lean_Elab_WF_GuessLex_generateMeasures___closed__2 = _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_generateMeasures___closed__2);
l_Lean_Elab_WF_GuessLex_generateMeasures___closed__3 = _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_generateMeasures___closed__3);
l_Lean_Elab_WF_GuessLex_generateMeasures___closed__4 = _init_l_Lean_Elab_WF_GuessLex_generateMeasures___closed__4();
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Elab_WF_GuessLex_solve_go___spec__2___rarg___closed__2);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__1 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__1);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__2 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__2);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__3 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__3);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__4);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__5);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__6 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__6);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__7);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__8);
l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__9 = _init_l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__9();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_mkTupleSyntax___closed__9);
l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_GuessLex_buildTermWF___spec__2___closed__6);
l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__4___closed__1);
l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_formatTable___spec__6___closed__1);
l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__1 = _init_l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__1);
l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__2 = _init_l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_RecCallWithContext_posString___closed__2);
l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Elab_WF_GuessLex_explainNonMutualFailure___spec__3___closed__1);
l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___closed__1 = _init_l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_explainNonMutualFailure___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_GuessLex_explainMutualFailure___spec__5___closed__10);
l_Lean_Elab_WF_GuessLex_explainFailure___closed__1 = _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_explainFailure___closed__1);
l_Lean_Elab_WF_GuessLex_explainFailure___closed__2 = _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_explainFailure___closed__2);
l_Lean_Elab_WF_GuessLex_explainFailure___closed__3 = _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_explainFailure___closed__3);
l_Lean_Elab_WF_GuessLex_explainFailure___closed__4 = _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_explainFailure___closed__4);
l_Lean_Elab_WF_GuessLex_explainFailure___closed__5 = _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_explainFailure___closed__5);
l_Lean_Elab_WF_GuessLex_explainFailure___closed__6 = _init_l_Lean_Elab_WF_GuessLex_explainFailure___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_GuessLex_explainFailure___closed__6);
l_Lean_Elab_WF_guessLex___lambda__2___closed__1 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__1);
l_Lean_Elab_WF_guessLex___lambda__2___closed__2 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__2);
l_Lean_Elab_WF_guessLex___lambda__2___closed__3 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__3);
l_Lean_Elab_WF_guessLex___lambda__2___closed__4 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__4);
l_Lean_Elab_WF_guessLex___lambda__2___closed__5 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__5);
l_Lean_Elab_WF_guessLex___lambda__2___closed__6 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__6);
l_Lean_Elab_WF_guessLex___lambda__2___closed__7 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__7);
l_Lean_Elab_WF_guessLex___lambda__2___closed__8 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__8);
l_Lean_Elab_WF_guessLex___lambda__2___closed__9 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__9);
l_Lean_Elab_WF_guessLex___lambda__2___closed__10 = _init_l_Lean_Elab_WF_guessLex___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___lambda__2___closed__10);
l_Lean_Elab_WF_guessLex___closed__1 = _init_l_Lean_Elab_WF_guessLex___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___closed__1);
l_Lean_Elab_WF_guessLex___closed__2 = _init_l_Lean_Elab_WF_guessLex___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_guessLex___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
