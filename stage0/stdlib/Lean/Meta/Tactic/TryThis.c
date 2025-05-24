// Lean compiler output
// Module: Lean.Meta.Tactic.TryThis
// Imports: Lean.Server.CodeActions Lean.Widget.UserWidget Lean.Data.Json.Elab Lean.Data.Lsp.Utf16 Lean.Meta.CollectFVars Lean.Meta.Tactic.ExposeNames Lean.Meta.TryThis Lean.Meta.Hint
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__72;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__15;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_pp_mvars;
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__50;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__1;
extern lean_object* l_Lean_Meta_Hint_tryThisDiffWidget;
lean_object* l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__16;
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__21;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__71;
static uint64_t l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__74;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__25;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__18;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__5;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__44;
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__2;
static lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__9;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__2;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__27;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__7;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__42;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_withoutRecover___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__69;
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextEdit(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__53;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__6;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__7;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5;
lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__64;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__55;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed__const__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__45;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__19;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
lean_object* l_Lean_Elab_Tactic_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__29;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85;
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__63;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__3;
lean_object* l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_625_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38;
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__12;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__20;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__65;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__16;
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__14;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__39;
static lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__8;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__77;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__54;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addTermSuggestions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__68;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__3;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1;
static lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__11;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__57;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__43;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__70;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__58;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__31;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36;
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__9;
lean_object* l_Lean_Meta_Tactic_TryThis_processSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__88;
static lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__60;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__67;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4;
lean_object* l_Lean_MessageData_ofConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__2(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__24;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__6;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1;
extern lean_object* l_Lean_warningAsError;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__1;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__75;
lean_object* l_Lean_Server_addBuiltinCodeActionProvider(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__14;
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__56;
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__51;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__30;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__73;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__41;
static lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__52;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3___boxed__const__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__34;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__47;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__26;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__37;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_savePanelWidgetInfo(uint64_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
static lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__79;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__83;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8;
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
static lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__1;
lean_object* l_Lean_Environment_mainModule(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__62;
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__8;
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4;
static lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__66;
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
static lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1;
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__61;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__76;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__49;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__23;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__32;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__5;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__89;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__80;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__3;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__59;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__17;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_pp_mvars_anonymous;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__12;
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__86;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__3;
lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__27;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__48;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExposedNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addTermSuggestions___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__8;
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__21;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__46;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__4;
lean_object* l_Array_toJson___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1586____spec__2(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__1;
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__81;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__2___boxed(lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__25;
static lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__3;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__35;
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__22;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure___at_Lean_Server_instRpcEncodableStateMRpcObjectStore___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__28;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__8;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nimport * as React from 'react';\nimport { EditorContext, EnvPosContext } from '@leanprover/infoview';\nconst e = React.createElement;\nexport default function ({ suggestions, range, header, isInline, style }) {\n  const pos = React.useContext(EnvPosContext)\n  const editorConnection = React.useContext(EditorContext)\n  const defStyle = style || {\n    className: 'link pointer dim',\n    style: { color: 'var(--vscode-textLink-foreground)' }\n  }\n\n  // Construct the children of the HTML element for a given suggestion.\n  function makeSuggestion({ suggestion, preInfo, postInfo, style }) {\n    function onClick() {\n      editorConnection.api.applyEdit({\n        changes: { [pos.uri]: [{ range, newText: suggestion }] }\n      })\n    }\n    return [\n      preInfo,\n      e('span', { onClick, title: 'Apply suggestion', ...style || defStyle }, suggestion),\n      postInfo\n    ]\n  }\n\n  // Choose between an inline 'Try this'-like display and a list-based 'Try these'-like display.\n  let inner = null\n  if (isInline) {\n    inner = e('div', { className: 'ml1' },\n      e('pre', { className: 'font-code pre-wrap' }, header, makeSuggestion(suggestions[0])))\n  } else {\n    inner = e('div', { className: 'ml1' },\n      e('pre', { className: 'font-code pre-wrap' }, header),\n      e('ul', { style: { paddingInlineStart: '20px' } }, suggestions.map(s =>\n        e('li', { className: 'font-code pre-wrap' }, makeSuggestion(s)))))\n  }\n  return e('details', { open: true },\n    e('summary', { className: 'mv2 pointer' }, 'Suggestions'),\n    inner)\n}", 1528, 1528);
return x_1;
}
}
static uint64_t _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__1;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__2;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TryThis", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tryThisWidget", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4;
x_5 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__6;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget;
x_4 = l_Lean_Widget_addBuiltinModule(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Hint", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tryThisDiffWidget", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2;
x_3 = l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1;
x_4 = l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3;
x_3 = l_Lean_Meta_Hint_tryThisDiffWidget;
x_4 = l_Lean_Widget_addBuiltinModule(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quickfix", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_nat_dec_lt(x_7, x_10);
if (x_11 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_3, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_7, x_17);
x_19 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_1);
lean_inc(x_14);
lean_inc(x_2);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_16);
x_21 = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(x_19, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
if (lean_obj_tag(x_15) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3;
x_24 = lean_string_append(x_23, x_14);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_26 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 5, x_16);
lean_ctor_set(x_26, 6, x_16);
lean_ctor_set(x_26, 7, x_22);
lean_ctor_set(x_26, 8, x_16);
lean_ctor_set(x_26, 9, x_16);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_26);
x_27 = lean_array_push(x_6, x_12);
x_28 = lean_ctor_get(x_5, 2);
x_29 = lean_nat_add(x_7, x_28);
lean_dec(x_7);
x_6 = x_27;
x_7 = x_29;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_32 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4;
x_33 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_16);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_16);
lean_ctor_set(x_33, 7, x_22);
lean_ctor_set(x_33, 8, x_16);
lean_ctor_set(x_33, 9, x_16);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_33);
x_34 = lean_array_push(x_6, x_12);
x_35 = lean_ctor_get(x_5, 2);
x_36 = lean_nat_add(x_7, x_35);
lean_dec(x_7);
x_6 = x_34;
x_7 = x_36;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
x_39 = lean_string_append(x_38, x_14);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_41 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_41, 0, x_16);
lean_ctor_set(x_41, 1, x_16);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_16);
lean_ctor_set(x_41, 5, x_16);
lean_ctor_set(x_41, 6, x_16);
lean_ctor_set(x_41, 7, x_22);
lean_ctor_set(x_41, 8, x_16);
lean_ctor_set(x_41, 9, x_16);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_41);
x_42 = lean_array_push(x_6, x_12);
x_43 = lean_ctor_get(x_5, 2);
x_44 = lean_nat_add(x_7, x_43);
lean_dec(x_7);
x_6 = x_42;
x_7 = x_44;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_47 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4;
x_48 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_48, 0, x_16);
lean_ctor_set(x_48, 1, x_16);
lean_ctor_set(x_48, 2, x_39);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set(x_48, 4, x_16);
lean_ctor_set(x_48, 5, x_47);
lean_ctor_set(x_48, 6, x_16);
lean_ctor_set(x_48, 7, x_22);
lean_ctor_set(x_48, 8, x_16);
lean_ctor_set(x_48, 9, x_16);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_48);
x_49 = lean_array_push(x_6, x_12);
x_50 = lean_ctor_get(x_5, 2);
x_51 = lean_nat_add(x_7, x_50);
lean_dec(x_7);
x_6 = x_49;
x_7 = x_51;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
}
}
else
{
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_15, 0);
lean_inc(x_53);
lean_dec(x_15);
x_54 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_55 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_55, 0, x_16);
lean_ctor_set(x_55, 1, x_16);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_16);
lean_ctor_set(x_55, 5, x_16);
lean_ctor_set(x_55, 6, x_16);
lean_ctor_set(x_55, 7, x_22);
lean_ctor_set(x_55, 8, x_16);
lean_ctor_set(x_55, 9, x_16);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_55);
x_56 = lean_array_push(x_6, x_12);
x_57 = lean_ctor_get(x_5, 2);
x_58 = lean_nat_add(x_7, x_57);
lean_dec(x_7);
x_6 = x_56;
x_7 = x_58;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_15, 0);
lean_inc(x_60);
lean_dec(x_15);
x_61 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_62 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4;
x_63 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_63, 0, x_16);
lean_ctor_set(x_63, 1, x_16);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_61);
lean_ctor_set(x_63, 4, x_16);
lean_ctor_set(x_63, 5, x_62);
lean_ctor_set(x_63, 6, x_16);
lean_ctor_set(x_63, 7, x_22);
lean_ctor_set(x_63, 8, x_16);
lean_ctor_set(x_63, 9, x_16);
lean_ctor_set(x_12, 1, x_16);
lean_ctor_set(x_12, 0, x_63);
x_64 = lean_array_push(x_6, x_12);
x_65 = lean_ctor_get(x_5, 2);
x_66 = lean_nat_add(x_7, x_65);
lean_dec(x_7);
x_6 = x_64;
x_7 = x_66;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_12, 0);
x_69 = lean_ctor_get(x_12, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_12);
x_70 = lean_box(0);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_eq(x_7, x_71);
x_73 = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(x_1);
lean_inc(x_68);
lean_inc(x_2);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_70);
x_75 = l_Lean_Lsp_WorkspaceEdit_ofTextEdit(x_73, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
if (lean_obj_tag(x_69) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3;
x_78 = lean_string_append(x_77, x_68);
lean_dec(x_68);
if (x_72 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_80 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_70);
lean_ctor_set(x_80, 2, x_78);
lean_ctor_set(x_80, 3, x_79);
lean_ctor_set(x_80, 4, x_70);
lean_ctor_set(x_80, 5, x_70);
lean_ctor_set(x_80, 6, x_70);
lean_ctor_set(x_80, 7, x_76);
lean_ctor_set(x_80, 8, x_70);
lean_ctor_set(x_80, 9, x_70);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_70);
x_82 = lean_array_push(x_6, x_81);
x_83 = lean_ctor_get(x_5, 2);
x_84 = lean_nat_add(x_7, x_83);
lean_dec(x_7);
x_6 = x_82;
x_7 = x_84;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_87 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4;
x_88 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_88, 0, x_70);
lean_ctor_set(x_88, 1, x_70);
lean_ctor_set(x_88, 2, x_78);
lean_ctor_set(x_88, 3, x_86);
lean_ctor_set(x_88, 4, x_70);
lean_ctor_set(x_88, 5, x_87);
lean_ctor_set(x_88, 6, x_70);
lean_ctor_set(x_88, 7, x_76);
lean_ctor_set(x_88, 8, x_70);
lean_ctor_set(x_88, 9, x_70);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_70);
x_90 = lean_array_push(x_6, x_89);
x_91 = lean_ctor_get(x_5, 2);
x_92 = lean_nat_add(x_7, x_91);
lean_dec(x_7);
x_6 = x_90;
x_7 = x_92;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_4, 0);
lean_inc(x_94);
x_95 = lean_string_append(x_94, x_68);
lean_dec(x_68);
if (x_72 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_97 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_97, 0, x_70);
lean_ctor_set(x_97, 1, x_70);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set(x_97, 4, x_70);
lean_ctor_set(x_97, 5, x_70);
lean_ctor_set(x_97, 6, x_70);
lean_ctor_set(x_97, 7, x_76);
lean_ctor_set(x_97, 8, x_70);
lean_ctor_set(x_97, 9, x_70);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_70);
x_99 = lean_array_push(x_6, x_98);
x_100 = lean_ctor_get(x_5, 2);
x_101 = lean_nat_add(x_7, x_100);
lean_dec(x_7);
x_6 = x_99;
x_7 = x_101;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_104 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4;
x_105 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_105, 0, x_70);
lean_ctor_set(x_105, 1, x_70);
lean_ctor_set(x_105, 2, x_95);
lean_ctor_set(x_105, 3, x_103);
lean_ctor_set(x_105, 4, x_70);
lean_ctor_set(x_105, 5, x_104);
lean_ctor_set(x_105, 6, x_70);
lean_ctor_set(x_105, 7, x_76);
lean_ctor_set(x_105, 8, x_70);
lean_ctor_set(x_105, 9, x_70);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_70);
x_107 = lean_array_push(x_6, x_106);
x_108 = lean_ctor_get(x_5, 2);
x_109 = lean_nat_add(x_7, x_108);
lean_dec(x_7);
x_6 = x_107;
x_7 = x_109;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
}
}
else
{
lean_dec(x_68);
if (x_72 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_69, 0);
lean_inc(x_111);
lean_dec(x_69);
x_112 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_113 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_113, 0, x_70);
lean_ctor_set(x_113, 1, x_70);
lean_ctor_set(x_113, 2, x_111);
lean_ctor_set(x_113, 3, x_112);
lean_ctor_set(x_113, 4, x_70);
lean_ctor_set(x_113, 5, x_70);
lean_ctor_set(x_113, 6, x_70);
lean_ctor_set(x_113, 7, x_76);
lean_ctor_set(x_113, 8, x_70);
lean_ctor_set(x_113, 9, x_70);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_70);
x_115 = lean_array_push(x_6, x_114);
x_116 = lean_ctor_get(x_5, 2);
x_117 = lean_nat_add(x_7, x_116);
lean_dec(x_7);
x_6 = x_115;
x_7 = x_117;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = lean_ctor_get(x_69, 0);
lean_inc(x_119);
lean_dec(x_69);
x_120 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2;
x_121 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4;
x_122 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_122, 0, x_70);
lean_ctor_set(x_122, 1, x_70);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_70);
lean_ctor_set(x_122, 5, x_121);
lean_ctor_set(x_122, 6, x_70);
lean_ctor_set(x_122, 7, x_76);
lean_ctor_set(x_122, 8, x_70);
lean_ctor_set(x_122, 9, x_70);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_70);
x_124 = lean_array_push(x_6, x_123);
x_125 = lean_ctor_get(x_5, 2);
x_126 = lean_nat_add(x_7, x_125);
lean_dec(x_7);
x_6 = x_124;
x_7 = x_126;
x_8 = lean_box(0);
x_9 = lean_box(0);
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1(x_2, x_3, x_1, x_4, x_10, x_5, x_8, lean_box(0), lean_box(0));
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_12, 0);
x_14 = lean_nat_dec_le(x_11, x_13);
if (x_14 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__1(x_1, x_2, x_3, x_4, x_5, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 9)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_ctor_get(x_6, 1);
x_9 = l_Lean_Meta_Tactic_TryThis_instTypeNameTryThisInfo;
x_10 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 0;
x_16 = l_Lean_Syntax_getRange_x3f(x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_FileMap_utf8RangeToLspRange(x_20, x_17);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_24, 1);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_nat_dec_le(x_23, x_26);
lean_dec(x_23);
if (x_27 == 0)
{
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__2(x_13, x_1, x_12, x_14, x_5, x_2, x_21, x_28);
lean_dec(x_21);
lean_dec(x_1);
lean_dec(x_13);
return x_29;
}
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_RequestM_readDoc___at_Lean_Server_RequestM_withWaitFindSnapAtPos___spec__1(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__3___boxed), 5, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_2);
x_10 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1;
x_11 = l_Lean_Elab_InfoTree_foldInfo___rarg(x_8, x_10, x_9);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__3___boxed), 5, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_1);
x_15 = l_Lean_Server_Snapshots_Snapshot_infoTree(x_2);
x_16 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1;
x_17 = l_Lean_Elab_InfoTree_foldInfo___rarg(x_14, x_16, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Tactic_TryThis_tryThisProvider(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tryThisProvider", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4;
x_5 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_tryThisProvider___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3;
x_4 = l_Lean_Server_addBuiltinCodeActionProvider(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_dec(x_13);
x_14 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1;
x_15 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_14);
lean_ctor_set(x_8, 4, x_15);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*13, x_2);
x_16 = l_Lean_PrettyPrinter_delab(x_3, x_4, x_5, x_6, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 3);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
x_26 = lean_ctor_get(x_8, 11);
x_27 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_8, 12);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_29 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1;
x_30 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_29);
x_31 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_1);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_20);
lean_ctor_set(x_31, 6, x_21);
lean_ctor_set(x_31, 7, x_22);
lean_ctor_set(x_31, 8, x_23);
lean_ctor_set(x_31, 9, x_24);
lean_ctor_set(x_31, 10, x_25);
lean_ctor_set(x_31, 11, x_26);
lean_ctor_set(x_31, 12, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_31, sizeof(void*)*13 + 1, x_27);
x_32 = l_Lean_PrettyPrinter_delab(x_3, x_4, x_5, x_6, x_31, x_9, x_10);
return x_32;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_mvars_anonymous;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_47; 
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
x_9 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1;
x_10 = 0;
x_11 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_8, x_9, x_10);
x_12 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2;
x_13 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_11, x_12);
x_14 = lean_st_ref_get(x_5, x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_47 = l_Lean_Kernel_isDiagnosticsEnabled(x_17);
lean_dec(x_17);
if (x_47 == 0)
{
if (x_13 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1(x_11, x_13, x_1, x_7, x_2, x_3, x_48, x_4, x_5, x_16);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_box(0);
x_18 = x_50;
goto block_46;
}
}
else
{
if (x_13 == 0)
{
lean_object* x_51; 
x_51 = lean_box(0);
x_18 = x_51;
goto block_46;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1(x_11, x_13, x_1, x_7, x_2, x_3, x_52, x_4, x_5, x_16);
return x_53;
}
}
block_46:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_18);
x_19 = lean_st_ref_take(x_5, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 5);
lean_dec(x_24);
x_25 = l_Lean_Kernel_enableDiag(x_23, x_13);
x_26 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5;
lean_ctor_set(x_20, 5, x_26);
lean_ctor_set(x_20, 0, x_25);
x_27 = lean_st_ref_set(x_5, x_20, x_21);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1(x_11, x_13, x_1, x_7, x_2, x_3, x_29, x_4, x_5, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_ctor_get(x_20, 2);
x_34 = lean_ctor_get(x_20, 3);
x_35 = lean_ctor_get(x_20, 4);
x_36 = lean_ctor_get(x_20, 6);
x_37 = lean_ctor_get(x_20, 7);
x_38 = lean_ctor_get(x_20, 8);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_39 = l_Lean_Kernel_enableDiag(x_31, x_13);
x_40 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5;
x_41 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_40);
lean_ctor_set(x_41, 6, x_36);
lean_ctor_set(x_41, 7, x_37);
lean_ctor_set(x_41, 8, x_38);
x_42 = lean_st_ref_set(x_5, x_41, x_21);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1(x_11, x_13, x_1, x_7, x_2, x_3, x_44, x_4, x_5, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_box(0);
x_13 = l_Lean_MessageData_ofExpr(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_14);
lean_ctor_set(x_15, 5, x_12);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__2;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
x_20 = lean_box(0);
x_21 = l_Lean_MessageData_ofExpr(x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 0);
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
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("suggestions", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("range", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isInline", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("style", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_1);
x_11 = x_1;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_5, 0);
lean_inc(x_103);
lean_dec(x_5);
x_11 = x_103;
goto block_102;
}
block_102:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = l_Lean_Syntax_getRange_x3f(x_11, x_12);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_Tactic_TryThis_processSuggestions(x_1, x_17, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint64_t x_53; lean_object* x_54; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_array_size(x_21);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__1(x_24, x_25, x_21);
x_27 = l_Array_toJson___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1586____spec__2(x_26);
x_28 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_625_(x_23);
x_31 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_tag(x_13, 3);
lean_ctor_set(x_13, 0, x_3);
x_33 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__3;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_13);
x_35 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_35, 0, x_4);
x_36 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__4;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Option_toJson___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__2(x_6);
x_39 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__5;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_29);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Json_mkObj(x_46);
x_48 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___spec__5(x_22, x_8, x_9, x_20);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Meta_Tactic_TryThis_tryThisWidget;
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
x_52 = lean_alloc_closure((void*)(l_StateT_pure___at_Lean_Server_instRpcEncodableStateMRpcObjectStore___spec__1___rarg), 2, 1);
lean_closure_set(x_52, 0, x_47);
x_53 = lean_unbox_uint64(x_51);
lean_dec(x_51);
x_54 = l_Lean_Widget_savePanelWidgetInfo(x_53, x_52, x_1, x_8, x_9, x_49);
lean_dec(x_9);
lean_dec(x_8);
return x_54;
}
else
{
uint8_t x_55; 
lean_free_object(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_13, 0);
lean_inc(x_59);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Lean_Meta_Tactic_TryThis_processSuggestions(x_1, x_59, x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint64_t x_96; lean_object* x_97; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_array_size(x_63);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__1(x_66, x_67, x_63);
x_69 = l_Array_toJson___at___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonCommand____x40_Lean_Data_Lsp_Basic___hyg_1586____spec__2(x_68);
x_70 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__1;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l___private_Lean_Data_Lsp_Basic_0__Lean_Lsp_toJsonRange____x40_Lean_Data_Lsp_Basic___hyg_625_(x_65);
x_73 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__2;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_3);
x_76 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__3;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_78, 0, x_4);
x_79 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__4;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Option_toJson___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__2(x_6);
x_82 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__5;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_71);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Json_mkObj(x_89);
x_91 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___spec__5(x_64, x_8, x_9, x_62);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_Meta_Tactic_TryThis_tryThisWidget;
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_95 = lean_alloc_closure((void*)(l_StateT_pure___at_Lean_Server_instRpcEncodableStateMRpcObjectStore___spec__1___rarg), 2, 1);
lean_closure_set(x_95, 0, x_90);
x_96 = lean_unbox_uint64(x_94);
lean_dec(x_94);
x_97 = l_Lean_Widget_savePanelWidgetInfo(x_96, x_95, x_1, x_8, x_9, x_92);
lean_dec(x_9);
lean_dec(x_8);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_ctor_get(x_60, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_60, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_100 = x_60;
} else {
 lean_dec_ref(x_60);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Option_toJson___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Option_toJson___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_stringToMessageData(x_4);
x_12 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = l_Lean_MessageData_ofSyntax(x_18);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_14);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_12);
x_22 = 0;
x_23 = 0;
lean_inc(x_8);
x_24 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_1, x_21, x_22, x_23, x_6, x_7, x_8, x_9, x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_24, 1);
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 1, x_28);
lean_ctor_set(x_24, 0, x_2);
x_29 = lean_array_mk(x_24);
x_30 = lean_box(0);
x_31 = 1;
x_32 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_29, x_4, x_31, x_3, x_30, x_5, x_8, x_9, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_array_mk(x_35);
x_37 = lean_box(0);
x_38 = 1;
x_39 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_36, x_4, x_38, x_3, x_37, x_5, x_8, x_9, x_33);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_dec(x_16);
x_41 = l_Lean_MessageData_ofSyntax(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
x_44 = 0;
x_45 = 0;
lean_inc(x_8);
x_46 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_1, x_43, x_44, x_45, x_6, x_7, x_8, x_9, x_10);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_48;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_mk(x_50);
x_52 = lean_box(0);
x_53 = 1;
x_54 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_51, x_4, x_53, x_3, x_52, x_5, x_8, x_9, x_47);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_16);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; uint8_t x_62; 
lean_ctor_set_tag(x_16, 3);
x_56 = l_Lean_MessageData_ofFormat(x_16);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_14);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_12);
x_59 = 0;
x_60 = 0;
lean_inc(x_8);
x_61 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_1, x_58, x_59, x_60, x_6, x_7, x_8, x_9, x_10);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 1, x_65);
lean_ctor_set(x_61, 0, x_2);
x_66 = lean_array_mk(x_61);
x_67 = lean_box(0);
x_68 = 1;
x_69 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_66, x_4, x_68, x_3, x_67, x_5, x_8, x_9, x_63);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_2);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_array_mk(x_72);
x_74 = lean_box(0);
x_75 = 1;
x_76 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_73, x_4, x_75, x_3, x_74, x_5, x_8, x_9, x_70);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_77 = lean_ctor_get(x_16, 0);
lean_inc(x_77);
lean_dec(x_16);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_14);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_12);
x_82 = 0;
x_83 = 0;
lean_inc(x_8);
x_84 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_1, x_81, x_82, x_83, x_6, x_7, x_8, x_9, x_10);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_86;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_2);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_array_mk(x_88);
x_90 = lean_box(0);
x_91 = 1;
x_92 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_89, x_4, x_91, x_3, x_90, x_5, x_8, x_9, x_85);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_ctor_get(x_15, 0);
lean_inc(x_93);
lean_dec(x_15);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_14);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_12);
x_96 = 0;
x_97 = 0;
lean_inc(x_8);
x_98 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_1, x_95, x_96, x_97, x_6, x_7, x_8, x_9, x_10);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_98, 1);
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
x_102 = lean_box(0);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 1, x_102);
lean_ctor_set(x_98, 0, x_2);
x_103 = lean_array_mk(x_98);
x_104 = lean_box(0);
x_105 = 1;
x_106 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_103, x_4, x_105, x_3, x_104, x_5, x_8, x_9, x_100);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_dec(x_98);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_2);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_mk(x_109);
x_111 = lean_box(0);
x_112 = 1;
x_113 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_1, x_110, x_4, x_112, x_3, x_111, x_5, x_8, x_9, x_107);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 4);
lean_inc(x_8);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_MessageData_ofSyntax(x_12);
x_14 = lean_array_uset(x_7, x_2, x_13);
x_2 = x_10;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_ctor_set_tag(x_11, 3);
x_17 = l_Lean_MessageData_ofFormat(x_11);
x_18 = lean_array_uset(x_7, x_2, x_17);
x_2 = x_10;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_MessageData_ofFormat(x_21);
x_23 = lean_array_uset(x_7, x_2, x_22);
x_2 = x_10;
x_3 = x_23;
goto _start;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_array_uset(x_7, x_2, x_25);
x_2 = x_10;
x_3 = x_26;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n• ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__2;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_array_size(x_1);
x_14 = 0;
lean_inc(x_1);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__1(x_13, x_14, x_1);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
x_19 = l_Lean_stringToMessageData(x_2);
x_20 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
if (x_18 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_16);
lean_dec(x_15);
x_23 = l_Lean_MessageData_nil;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
x_26 = 0;
x_27 = 0;
lean_inc(x_10);
x_28 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_3, x_25, x_26, x_27, x_8, x_9, x_10, x_11, x_12);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_3, x_1, x_2, x_27, x_4, x_5, x_6, x_10, x_11, x_29);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_16, x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_16);
lean_dec(x_15);
x_32 = l_Lean_MessageData_nil;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_20);
x_35 = 0;
x_36 = 0;
lean_inc(x_10);
x_37 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_3, x_34, x_35, x_36, x_8, x_9, x_10, x_11, x_12);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_3, x_1, x_2, x_36, x_4, x_5, x_6, x_10, x_11, x_38);
return x_39;
}
else
{
size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_41 = l_Lean_MessageData_nil;
x_42 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2(x_15, x_14, x_40, x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_22);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_20);
x_45 = 0;
x_46 = 0;
lean_inc(x_10);
x_47 = l_Lean_logAt___at_Lean_Elab_Term_reportUnsolvedGoals___spec__2(x_3, x_44, x_45, x_46, x_8, x_9, x_10, x_11, x_12);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore(x_3, x_1, x_2, x_46, x_4, x_5, x_6, x_10, x_11, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no suggestions available", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Array_isEmpty___rarg(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Tactic_TryThis_addSuggestions___lambda__1(x_2, x_4, x_1, x_3, x_5, x_6, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__2;
x_16 = l_Lean_throwErrorAt___at_Lean_Meta_Match_Alt_checkAndReplaceFVarId___spec__3(x_1, x_15, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Tactic_TryThis_addSuggestions___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_2(x_1, x_2, x_3);
x_12 = l_Lean_Elab_Term_withoutErrToSorryImp___rarg(x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic did not produce expected goal", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_29; lean_object* x_30; lean_object* x_37; 
x_13 = l_Lean_Elab_Tactic_saveState___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l_Lean_Elab_Tactic_SavedState_restore(x_1, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic), 10, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withoutRecover___rarg), 10, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_Elab_Term_withoutErrToSorry___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___spec__1(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_37) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_21 = x_39;
x_22 = x_38;
goto block_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_MVarId_getType(x_43, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_41, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_expr_eqv(x_49, x_52);
lean_dec(x_52);
lean_dec(x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__2;
x_56 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_29 = x_57;
x_30 = x_58;
goto block_36;
}
else
{
lean_object* x_59; 
x_59 = lean_box(0);
x_21 = x_59;
x_22 = x_53;
goto block_28;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_41);
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
lean_dec(x_45);
x_29 = x_60;
x_30 = x_61;
goto block_36;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_41);
x_62 = lean_ctor_get(x_42, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_dec(x_42);
x_29 = x_62;
x_30 = x_63;
goto block_36;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_37, 1);
lean_inc(x_65);
lean_dec(x_37);
x_29 = x_64;
x_30 = x_65;
goto block_36;
}
block_28:
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
block_36:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_14, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exposeNames", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expose_names", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(";", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(expose_names; ", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_18 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
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
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; uint8_t x_32; 
lean_free_object(x_18);
lean_dec(x_26);
x_30 = 0;
x_31 = l_Lean_Elab_Tactic_SavedState_restore(x_16, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 5);
lean_inc(x_35);
x_36 = l_Lean_SourceInfo_fromRef(x_35, x_30);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_12, x_33);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4;
lean_inc(x_36);
lean_ctor_set_tag(x_37, 2);
lean_ctor_set(x_37, 1, x_41);
lean_ctor_set(x_37, 0, x_36);
x_42 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13;
lean_inc(x_36);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_42);
lean_ctor_set(x_31, 0, x_36);
x_43 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12;
lean_inc(x_36);
x_44 = l_Lean_Syntax_node1(x_36, x_43, x_31);
x_45 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
lean_inc(x_36);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_45);
lean_ctor_set(x_14, 0, x_36);
x_46 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_36);
x_47 = l_Lean_Syntax_node3(x_36, x_46, x_44, x_14, x_1);
x_48 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8;
lean_inc(x_36);
x_49 = l_Lean_Syntax_node1(x_36, x_48, x_47);
x_50 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6;
lean_inc(x_36);
x_51 = l_Lean_Syntax_node1(x_36, x_50, x_49);
x_52 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
lean_inc(x_36);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_36);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3;
x_55 = l_Lean_Syntax_node3(x_36, x_54, x_37, x_51, x_53);
x_56 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_55);
x_60 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 0, x_63);
x_64 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_60, 0, x_67);
return x_60;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_dec(x_60);
x_69 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 0, x_69);
x_70 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_55);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_68);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_free_object(x_56);
lean_dec(x_55);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_60);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_60, 0);
x_77 = lean_ctor_get(x_60, 1);
x_78 = l_Lean_Exception_isInterrupt(x_76);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Exception_isRuntime(x_76);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
lean_free_object(x_60);
lean_dec(x_76);
x_80 = l_Lean_Elab_Tactic_SavedState_restore(x_58, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = lean_box(0);
lean_ctor_set(x_80, 0, x_83);
return x_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_60;
}
}
else
{
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_60;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_60, 0);
x_88 = lean_ctor_get(x_60, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_60);
x_89 = l_Lean_Exception_isInterrupt(x_87);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Exception_isRuntime(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_87);
x_91 = l_Lean_Elab_Tactic_SavedState_restore(x_58, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_88);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_94 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
return x_95;
}
else
{
lean_object* x_96; 
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_88);
return x_96;
}
}
else
{
lean_object* x_97; 
lean_dec(x_58);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_56, 0);
x_99 = lean_ctor_get(x_56, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_56);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_55);
x_100 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_98);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_2);
x_105 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_55);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
if (lean_is_scalar(x_102)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_102;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_101);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_55);
lean_dec(x_2);
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_112 = x_100;
} else {
 lean_dec_ref(x_100);
 x_112 = lean_box(0);
}
x_113 = l_Lean_Exception_isInterrupt(x_110);
if (x_113 == 0)
{
uint8_t x_114; 
x_114 = l_Lean_Exception_isRuntime(x_110);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_112);
lean_dec(x_110);
x_115 = l_Lean_Elab_Tactic_SavedState_restore(x_98, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_111);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; 
lean_dec(x_98);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_112)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_112;
}
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_111);
return x_120;
}
}
else
{
lean_object* x_121; 
lean_dec(x_98);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_112)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_112;
}
lean_ctor_set(x_121, 0, x_110);
lean_ctor_set(x_121, 1, x_111);
return x_121;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_122 = lean_ctor_get(x_37, 1);
lean_inc(x_122);
lean_dec(x_37);
x_123 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4;
lean_inc(x_36);
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_36);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13;
lean_inc(x_36);
lean_ctor_set_tag(x_31, 2);
lean_ctor_set(x_31, 1, x_125);
lean_ctor_set(x_31, 0, x_36);
x_126 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12;
lean_inc(x_36);
x_127 = l_Lean_Syntax_node1(x_36, x_126, x_31);
x_128 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
lean_inc(x_36);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_128);
lean_ctor_set(x_14, 0, x_36);
x_129 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_36);
x_130 = l_Lean_Syntax_node3(x_36, x_129, x_127, x_14, x_1);
x_131 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8;
lean_inc(x_36);
x_132 = l_Lean_Syntax_node1(x_36, x_131, x_130);
x_133 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6;
lean_inc(x_36);
x_134 = l_Lean_Syntax_node1(x_36, x_133, x_132);
x_135 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
lean_inc(x_36);
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_36);
lean_ctor_set(x_136, 1, x_135);
x_137 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3;
x_138 = l_Lean_Syntax_node3(x_36, x_137, x_124, x_134, x_136);
x_139 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_122);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_138);
x_143 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_138, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_146 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(7, 2, 0);
} else {
 x_147 = x_142;
 lean_ctor_set_tag(x_147, 7);
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_2);
x_148 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_138);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_144);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_142);
lean_dec(x_138);
lean_dec(x_2);
x_153 = lean_ctor_get(x_143, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_143, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_155 = x_143;
} else {
 lean_dec_ref(x_143);
 x_155 = lean_box(0);
}
x_156 = l_Lean_Exception_isInterrupt(x_153);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = l_Lean_Exception_isRuntime(x_153);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_155);
lean_dec(x_153);
x_158 = l_Lean_Elab_Tactic_SavedState_restore(x_140, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_154);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
x_161 = lean_box(0);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
return x_162;
}
else
{
lean_object* x_163; 
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_155)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_155;
}
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_154);
return x_163;
}
}
else
{
lean_object* x_164; 
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_155)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_155;
}
lean_ctor_set(x_164, 0, x_153);
lean_ctor_set(x_164, 1, x_154);
return x_164;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_165 = lean_ctor_get(x_31, 1);
lean_inc(x_165);
lean_dec(x_31);
x_166 = lean_ctor_get(x_11, 5);
lean_inc(x_166);
x_167 = l_Lean_SourceInfo_fromRef(x_166, x_30);
lean_dec(x_166);
x_168 = lean_st_ref_get(x_12, x_165);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4;
lean_inc(x_167);
if (lean_is_scalar(x_170)) {
 x_172 = lean_alloc_ctor(2, 2, 0);
} else {
 x_172 = x_170;
 lean_ctor_set_tag(x_172, 2);
}
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_171);
x_173 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13;
lean_inc(x_167);
x_174 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_173);
x_175 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12;
lean_inc(x_167);
x_176 = l_Lean_Syntax_node1(x_167, x_175, x_174);
x_177 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
lean_inc(x_167);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_177);
lean_ctor_set(x_14, 0, x_167);
x_178 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_167);
x_179 = l_Lean_Syntax_node3(x_167, x_178, x_176, x_14, x_1);
x_180 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8;
lean_inc(x_167);
x_181 = l_Lean_Syntax_node1(x_167, x_180, x_179);
x_182 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6;
lean_inc(x_167);
x_183 = l_Lean_Syntax_node1(x_167, x_182, x_181);
x_184 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
lean_inc(x_167);
x_185 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_185, 0, x_167);
lean_ctor_set(x_185, 1, x_184);
x_186 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3;
x_187 = l_Lean_Syntax_node3(x_167, x_186, x_172, x_183, x_185);
x_188 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_169);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_187);
x_192 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_187, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_189);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(7, 2, 0);
} else {
 x_196 = x_191;
 lean_ctor_set_tag(x_196, 7);
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_2);
x_197 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_187);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
if (lean_is_scalar(x_194)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_194;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_193);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_191);
lean_dec(x_187);
lean_dec(x_2);
x_202 = lean_ctor_get(x_192, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_192, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_204 = x_192;
} else {
 lean_dec_ref(x_192);
 x_204 = lean_box(0);
}
x_205 = l_Lean_Exception_isInterrupt(x_202);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = l_Lean_Exception_isRuntime(x_202);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_204);
lean_dec(x_202);
x_207 = l_Lean_Elab_Tactic_SavedState_restore(x_189, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_203);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
x_210 = lean_box(0);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
return x_211;
}
else
{
lean_object* x_212; 
lean_dec(x_189);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_204)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_204;
}
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_203);
return x_212;
}
}
else
{
lean_object* x_213; 
lean_dec(x_189);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_204)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_204;
}
lean_ctor_set(x_213, 0, x_202);
lean_ctor_set(x_213, 1, x_203);
return x_213;
}
}
}
}
else
{
lean_free_object(x_14);
lean_dec(x_16);
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
lean_dec(x_1);
return x_18;
}
}
else
{
lean_free_object(x_14);
lean_dec(x_16);
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
lean_dec(x_1);
return x_18;
}
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_18, 0);
x_215 = lean_ctor_get(x_18, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_18);
x_216 = l_Lean_Exception_isInterrupt(x_214);
if (x_216 == 0)
{
uint8_t x_217; 
x_217 = l_Lean_Exception_isRuntime(x_214);
if (x_217 == 0)
{
uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_214);
x_218 = 0;
x_219 = l_Lean_Elab_Tactic_SavedState_restore(x_16, x_218, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_215);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_11, 5);
lean_inc(x_222);
x_223 = l_Lean_SourceInfo_fromRef(x_222, x_218);
lean_dec(x_222);
x_224 = lean_st_ref_get(x_12, x_220);
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
x_227 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4;
lean_inc(x_223);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(2, 2, 0);
} else {
 x_228 = x_226;
 lean_ctor_set_tag(x_228, 2);
}
lean_ctor_set(x_228, 0, x_223);
lean_ctor_set(x_228, 1, x_227);
x_229 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13;
lean_inc(x_223);
if (lean_is_scalar(x_221)) {
 x_230 = lean_alloc_ctor(2, 2, 0);
} else {
 x_230 = x_221;
 lean_ctor_set_tag(x_230, 2);
}
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_229);
x_231 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12;
lean_inc(x_223);
x_232 = l_Lean_Syntax_node1(x_223, x_231, x_230);
x_233 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
lean_inc(x_223);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_233);
lean_ctor_set(x_14, 0, x_223);
x_234 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_223);
x_235 = l_Lean_Syntax_node3(x_223, x_234, x_232, x_14, x_1);
x_236 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8;
lean_inc(x_223);
x_237 = l_Lean_Syntax_node1(x_223, x_236, x_235);
x_238 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6;
lean_inc(x_223);
x_239 = l_Lean_Syntax_node1(x_223, x_238, x_237);
x_240 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
lean_inc(x_223);
x_241 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_241, 0, x_223);
lean_ctor_set(x_241, 1, x_240);
x_242 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3;
x_243 = l_Lean_Syntax_node3(x_223, x_242, x_228, x_239, x_241);
x_244 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_225);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_243);
x_248 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_243, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_246);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_245);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
x_251 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
if (lean_is_scalar(x_247)) {
 x_252 = lean_alloc_ctor(7, 2, 0);
} else {
 x_252 = x_247;
 lean_ctor_set_tag(x_252, 7);
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_2);
x_253 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_243);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
if (lean_is_scalar(x_250)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_250;
}
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_249);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_dec(x_247);
lean_dec(x_243);
lean_dec(x_2);
x_258 = lean_ctor_get(x_248, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_248, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_260 = x_248;
} else {
 lean_dec_ref(x_248);
 x_260 = lean_box(0);
}
x_261 = l_Lean_Exception_isInterrupt(x_258);
if (x_261 == 0)
{
uint8_t x_262; 
x_262 = l_Lean_Exception_isRuntime(x_258);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_260);
lean_dec(x_258);
x_263 = l_Lean_Elab_Tactic_SavedState_restore(x_245, x_218, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_259);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
x_266 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
return x_267;
}
else
{
lean_object* x_268; 
lean_dec(x_245);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_260)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_260;
}
lean_ctor_set(x_268, 0, x_258);
lean_ctor_set(x_268, 1, x_259);
return x_268;
}
}
else
{
lean_object* x_269; 
lean_dec(x_245);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_260)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_260;
}
lean_ctor_set(x_269, 0, x_258);
lean_ctor_set(x_269, 1, x_259);
return x_269;
}
}
}
else
{
lean_object* x_270; 
lean_free_object(x_14);
lean_dec(x_16);
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
lean_dec(x_1);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_214);
lean_ctor_set(x_270, 1, x_215);
return x_270;
}
}
else
{
lean_object* x_271; 
lean_free_object(x_14);
lean_dec(x_16);
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
lean_dec(x_1);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_214);
lean_ctor_set(x_271, 1, x_215);
return x_271;
}
}
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_14, 0);
x_273 = lean_ctor_get(x_14, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_3);
x_274 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_272);
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
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_276 = x_274;
} else {
 lean_dec_ref(x_274);
 x_276 = lean_box(0);
}
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_1);
lean_ctor_set(x_277, 1, x_2);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
if (lean_is_scalar(x_276)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_276;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_275);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_280 = lean_ctor_get(x_274, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_274, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_282 = x_274;
} else {
 lean_dec_ref(x_274);
 x_282 = lean_box(0);
}
x_283 = l_Lean_Exception_isInterrupt(x_280);
if (x_283 == 0)
{
uint8_t x_284; 
x_284 = l_Lean_Exception_isRuntime(x_280);
if (x_284 == 0)
{
uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_282);
lean_dec(x_280);
x_285 = 0;
x_286 = l_Lean_Elab_Tactic_SavedState_restore(x_272, x_285, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_281);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_288 = x_286;
} else {
 lean_dec_ref(x_286);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_11, 5);
lean_inc(x_289);
x_290 = l_Lean_SourceInfo_fromRef(x_289, x_285);
lean_dec(x_289);
x_291 = lean_st_ref_get(x_12, x_287);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
x_294 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4;
lean_inc(x_290);
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(2, 2, 0);
} else {
 x_295 = x_293;
 lean_ctor_set_tag(x_295, 2);
}
lean_ctor_set(x_295, 0, x_290);
lean_ctor_set(x_295, 1, x_294);
x_296 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13;
lean_inc(x_290);
if (lean_is_scalar(x_288)) {
 x_297 = lean_alloc_ctor(2, 2, 0);
} else {
 x_297 = x_288;
 lean_ctor_set_tag(x_297, 2);
}
lean_ctor_set(x_297, 0, x_290);
lean_ctor_set(x_297, 1, x_296);
x_298 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12;
lean_inc(x_290);
x_299 = l_Lean_Syntax_node1(x_290, x_298, x_297);
x_300 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14;
lean_inc(x_290);
x_301 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_301, 0, x_290);
lean_ctor_set(x_301, 1, x_300);
x_302 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_290);
x_303 = l_Lean_Syntax_node3(x_290, x_302, x_299, x_301, x_1);
x_304 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8;
lean_inc(x_290);
x_305 = l_Lean_Syntax_node1(x_290, x_304, x_303);
x_306 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6;
lean_inc(x_290);
x_307 = l_Lean_Syntax_node1(x_290, x_306, x_305);
x_308 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15;
lean_inc(x_290);
x_309 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_309, 0, x_290);
lean_ctor_set(x_309, 1, x_308);
x_310 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3;
x_311 = l_Lean_Syntax_node3(x_290, x_310, x_295, x_307, x_309);
x_312 = l_Lean_Elab_Tactic_saveState___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_292);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_311);
x_316 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState(x_3, x_311, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_314);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_313);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_318 = x_316;
} else {
 lean_dec_ref(x_316);
 x_318 = lean_box(0);
}
x_319 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
if (lean_is_scalar(x_315)) {
 x_320 = lean_alloc_ctor(7, 2, 0);
} else {
 x_320 = x_315;
 lean_ctor_set_tag(x_320, 7);
}
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_2);
x_321 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
x_322 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_311);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_323);
if (lean_is_scalar(x_318)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_318;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_317);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
lean_dec(x_315);
lean_dec(x_311);
lean_dec(x_2);
x_326 = lean_ctor_get(x_316, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_316, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_328 = x_316;
} else {
 lean_dec_ref(x_316);
 x_328 = lean_box(0);
}
x_329 = l_Lean_Exception_isInterrupt(x_326);
if (x_329 == 0)
{
uint8_t x_330; 
x_330 = l_Lean_Exception_isRuntime(x_326);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_328);
lean_dec(x_326);
x_331 = l_Lean_Elab_Tactic_SavedState_restore(x_313, x_285, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_327);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
x_334 = lean_box(0);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_332);
return x_335;
}
else
{
lean_object* x_336; 
lean_dec(x_313);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_328)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_328;
}
lean_ctor_set(x_336, 0, x_326);
lean_ctor_set(x_336, 1, x_327);
return x_336;
}
}
else
{
lean_object* x_337; 
lean_dec(x_313);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_328)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_328;
}
lean_ctor_set(x_337, 0, x_326);
lean_ctor_set(x_337, 1, x_327);
return x_337;
}
}
}
else
{
lean_object* x_338; 
lean_dec(x_272);
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
lean_dec(x_1);
if (lean_is_scalar(x_282)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_282;
}
lean_ctor_set(x_338, 0, x_280);
lean_ctor_set(x_338, 1, x_281);
return x_338;
}
}
else
{
lean_object* x_339; 
lean_dec(x_272);
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
lean_dec(x_1);
if (lean_is_scalar(x_282)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_282;
}
lean_ctor_set(x_339, 0, x_280);
lean_ctor_set(x_339, 1, x_281);
return x_339;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found ", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", but the corresponding tactic failed:", 38, 38);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\nIt may be possible to correct this proof by adding type annotations, explicitly specifying implicit arguments, or eliminating unnecessary function abstractions.", 162, 162);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2;
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_indentD(x_2);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__6;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact ", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refine ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_MessageData_ofExpr(x_1);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_9, x_4, x_5, x_6, x_7, x_8);
if (x_2 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refine", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
if (x_2 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_5, 5);
lean_inc(x_11);
x_12 = 0;
x_13 = l_Lean_SourceInfo_fromRef(x_11, x_12);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_6, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1;
lean_inc(x_13);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_13);
x_19 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__2;
x_20 = l_Lean_Syntax_node2(x_13, x_19, x_14, x_9);
x_21 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1(x_1, x_2, x_20, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1;
lean_inc(x_13);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__2;
x_26 = l_Lean_Syntax_node2(x_13, x_25, x_24, x_9);
x_27 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1(x_1, x_2, x_26, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_5, 5);
lean_inc(x_30);
x_31 = 0;
x_32 = l_Lean_SourceInfo_fromRef(x_30, x_31);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_6, x_29);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3;
lean_inc(x_32);
lean_ctor_set_tag(x_33, 2);
lean_ctor_set(x_33, 1, x_37);
lean_ctor_set(x_33, 0, x_32);
x_38 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__4;
x_39 = l_Lean_Syntax_node2(x_32, x_38, x_33, x_28);
x_40 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1(x_1, x_2, x_39, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3;
lean_inc(x_32);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__4;
x_45 = l_Lean_Syntax_node2(x_32, x_44, x_43, x_28);
x_46 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1(x_1, x_2, x_45, x_3, x_4, x_5, x_6, x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
return x_8;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 0);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_8);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_dec(x_12);
x_13 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1;
x_14 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_13);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*13, x_2);
x_15 = l_Lean_Meta_withExposedNames___rarg(x_3, x_4, x_5, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
x_18 = lean_ctor_get(x_7, 3);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_7, 12);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_28 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1;
x_29 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_28);
x_30 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_1);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_19);
lean_ctor_set(x_30, 6, x_20);
lean_ctor_set(x_30, 7, x_21);
lean_ctor_set(x_30, 8, x_22);
lean_ctor_set(x_30, 9, x_23);
lean_ctor_set(x_30, 10, x_24);
lean_ctor_set(x_30, 11, x_25);
lean_ctor_set(x_30, 12, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_30, sizeof(void*)*13 + 1, x_26);
x_31 = l_Lean_Meta_withExposedNames___rarg(x_3, x_4, x_5, x_30, x_8, x_9);
return x_31;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_mvars;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_49; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___closed__1;
x_12 = 0;
x_13 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_10, x_11, x_12);
x_14 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_13, x_14);
x_16 = lean_st_ref_get(x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_49 = l_Lean_Kernel_isDiagnosticsEnabled(x_19);
lean_dec(x_19);
if (x_49 == 0)
{
if (x_15 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3(x_13, x_15, x_9, x_3, x_4, x_50, x_5, x_6, x_18);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_20 = x_52;
goto block_48;
}
}
else
{
if (x_15 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_20 = x_53;
goto block_48;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
x_55 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3(x_13, x_15, x_9, x_3, x_4, x_54, x_5, x_6, x_18);
return x_55;
}
}
block_48:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_20);
x_21 = lean_st_ref_take(x_6, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 5);
lean_dec(x_26);
x_27 = l_Lean_Kernel_enableDiag(x_25, x_15);
x_28 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5;
lean_ctor_set(x_22, 5, x_28);
lean_ctor_set(x_22, 0, x_27);
x_29 = lean_st_ref_set(x_6, x_22, x_23);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3(x_13, x_15, x_9, x_3, x_4, x_31, x_5, x_6, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
x_37 = lean_ctor_get(x_22, 4);
x_38 = lean_ctor_get(x_22, 6);
x_39 = lean_ctor_get(x_22, 7);
x_40 = lean_ctor_get(x_22, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_41 = l_Lean_Kernel_enableDiag(x_33, x_15);
x_42 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5;
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_34);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_36);
lean_ctor_set(x_43, 4, x_37);
lean_ctor_set(x_43, 5, x_42);
lean_ctor_set(x_43, 6, x_38);
lean_ctor_set(x_43, 7, x_39);
lean_ctor_set(x_43, 8, x_40);
x_44 = lean_st_ref_set(x_6, x_43, x_23);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3(x_13, x_15, x_9, x_3, x_4, x_46, x_5, x_6, x_45);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n⊢ ", 5, 3);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_3, x_5);
x_19 = l_Lean_MVarId_getType(x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instantiateMVars___at_Lean_Elab_Tactic_getMainTarget___spec__1(x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr), 6, 1);
lean_closure_set(x_26, 0, x_24);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_27 = l_Lean_Meta_withExposedNames___rarg(x_26, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__2;
lean_ctor_set_tag(x_22, 5);
lean_ctor_set(x_22, 1, x_28);
lean_ctor_set(x_22, 0, x_30);
x_31 = l_Std_Format_defWidth;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_format_pretty(x_22, x_31, x_32, x_32);
x_34 = lean_string_append(x_6, x_33);
lean_dec(x_33);
x_35 = 1;
x_36 = lean_usize_add(x_5, x_35);
x_5 = x_36;
x_6 = x_34;
x_15 = x_29;
goto _start;
}
else
{
uint8_t x_38; 
lean_free_object(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_22, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_22);
x_44 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr), 6, 1);
lean_closure_set(x_44, 0, x_42);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_45 = l_Lean_Meta_withExposedNames___rarg(x_44, x_11, x_12, x_13, x_14, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__2;
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
x_50 = l_Std_Format_defWidth;
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_format_pretty(x_49, x_50, x_51, x_51);
x_53 = lean_string_append(x_6, x_52);
lean_dec(x_52);
x_54 = 1;
x_55 = lean_usize_add(x_5, x_54);
x_5 = x_55;
x_6 = x_53;
x_15 = x_47;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_59 = x_45;
} else {
 lean_dec_ref(x_45);
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
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
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
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
lean_inc_n(x_3, 2);
x_17 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_16);
lean_ctor_set(x_17, 5, x_3);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proof", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__2;
x_2 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__5;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partial ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__2;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__8;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__9;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nRemaining subgoals:", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_232; 
x_17 = lean_ctor_get(x_13, 4);
lean_dec(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_dec(x_18);
x_19 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1;
x_20 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_19);
lean_ctor_set(x_13, 4, x_20);
lean_ctor_set(x_13, 2, x_1);
lean_ctor_set_uint8(x_13, sizeof(void*)*13, x_2);
lean_inc(x_3);
x_21 = l_Lean_Meta_getMVars(x_3, x_4, x_5, x_13, x_14, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_232 = l_Array_isEmpty___rarg(x_22);
if (x_232 == 0)
{
uint8_t x_233; 
x_233 = 1;
x_25 = x_233;
goto block_231;
}
else
{
uint8_t x_234; 
x_234 = 0;
x_25 = x_234;
goto block_231;
}
block_231:
{
lean_object* x_26; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(x_3, x_25, x_4, x_5, x_13, x_14, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_dec(x_32);
x_33 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
lean_ctor_set(x_27, 1, x_31);
lean_ctor_set(x_27, 0, x_33);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_26, 0, x_42);
return x_26;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_45 = x_27;
} else {
 lean_dec_ref(x_27);
 x_45 = lean_box(0);
}
x_46 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_dec(x_26);
x_53 = !lean_is_exclusive(x_27);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_6);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_27, 0);
x_56 = lean_ctor_get(x_27, 1);
x_57 = lean_ctor_get(x_6, 0);
x_58 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_56);
x_59 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_55, x_56, x_57, x_58, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_52);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
x_63 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 0, x_63);
x_64 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
if (lean_is_scalar(x_24)) {
 x_65 = lean_alloc_ctor(7, 2, 0);
} else {
 x_65 = x_24;
 lean_ctor_set_tag(x_65, 7);
}
lean_ctor_set(x_65, 0, x_27);
lean_ctor_set(x_65, 1, x_64);
if (x_25 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6;
x_67 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_66, x_65);
lean_ctor_set(x_6, 0, x_67);
lean_ctor_set(x_59, 0, x_6);
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10;
x_69 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_68, x_65);
lean_ctor_set(x_6, 0, x_69);
lean_ctor_set(x_59, 0, x_6);
return x_59;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_dec(x_59);
x_71 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 0, x_71);
x_72 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
if (lean_is_scalar(x_24)) {
 x_73 = lean_alloc_ctor(7, 2, 0);
} else {
 x_73 = x_24;
 lean_ctor_set_tag(x_73, 7);
}
lean_ctor_set(x_73, 0, x_27);
lean_ctor_set(x_73, 1, x_72);
if (x_25 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6;
x_75 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_74, x_73);
lean_ctor_set(x_6, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_6);
lean_ctor_set(x_76, 1, x_70);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10;
x_78 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_77, x_73);
lean_ctor_set(x_6, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_6);
lean_ctor_set(x_79, 1, x_70);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_free_object(x_6);
lean_free_object(x_27);
lean_dec(x_56);
lean_dec(x_24);
x_80 = !lean_is_exclusive(x_60);
if (x_80 == 0)
{
if (x_11 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_60, 0);
lean_free_object(x_60);
lean_dec(x_22);
x_82 = lean_ctor_get(x_59, 1);
lean_inc(x_82);
lean_dec(x_59);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_83, x_84, x_58, x_58, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_82);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_60, 0);
x_87 = lean_ctor_get(x_59, 1);
lean_inc(x_87);
lean_dec(x_59);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Array_isEmpty___rarg(x_22);
if (x_90 == 0)
{
lean_object* x_91; size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_box(0);
x_92 = lean_array_size(x_22);
x_93 = 0;
x_94 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
x_95 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(x_22, x_91, x_22, x_92, x_93, x_94, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_87);
lean_dec(x_22);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_ctor_set(x_60, 0, x_96);
x_98 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_88, x_89, x_58, x_60, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_97);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_89);
lean_dec(x_88);
lean_free_object(x_60);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; 
lean_free_object(x_60);
lean_dec(x_22);
x_103 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_88, x_89, x_58, x_58, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_87);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_103;
}
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_60, 0);
lean_inc(x_104);
lean_dec(x_60);
if (x_11 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_22);
x_105 = lean_ctor_get(x_59, 1);
lean_inc(x_105);
lean_dec(x_59);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_106, x_107, x_58, x_58, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_105);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_ctor_get(x_59, 1);
lean_inc(x_109);
lean_dec(x_59);
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_dec(x_104);
x_112 = l_Array_isEmpty___rarg(x_22);
if (x_112 == 0)
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; 
x_113 = lean_box(0);
x_114 = lean_array_size(x_22);
x_115 = 0;
x_116 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
x_117 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(x_22, x_113, x_22, x_114, x_115, x_116, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_109);
lean_dec(x_22);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_118);
x_121 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_110, x_111, x_58, x_120, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_119);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_124 = x_117;
} else {
 lean_dec_ref(x_117);
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
lean_object* x_126; 
lean_dec(x_22);
x_126 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_110, x_111, x_58, x_58, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_109);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_126;
}
}
}
}
}
else
{
uint8_t x_127; 
lean_free_object(x_6);
lean_free_object(x_27);
lean_dec(x_56);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_59);
if (x_127 == 0)
{
return x_59;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_59, 0);
x_129 = lean_ctor_get(x_59, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_59);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_27, 0);
x_132 = lean_ctor_get(x_27, 1);
x_133 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
lean_dec(x_6);
x_134 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_132);
x_135 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_131, x_132, x_133, x_134, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_52);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 0, x_139);
x_140 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
if (lean_is_scalar(x_24)) {
 x_141 = lean_alloc_ctor(7, 2, 0);
} else {
 x_141 = x_24;
 lean_ctor_set_tag(x_141, 7);
}
lean_ctor_set(x_141, 0, x_27);
lean_ctor_set(x_141, 1, x_140);
if (x_25 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6;
x_143 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_142, x_141);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10;
x_147 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_146, x_141);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
if (lean_is_scalar(x_138)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_138;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_137);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_free_object(x_27);
lean_dec(x_132);
lean_dec(x_24);
x_150 = lean_ctor_get(x_136, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_151 = x_136;
} else {
 lean_dec_ref(x_136);
 x_151 = lean_box(0);
}
if (x_11 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_151);
lean_dec(x_22);
x_152 = lean_ctor_get(x_135, 1);
lean_inc(x_152);
lean_dec(x_135);
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
x_155 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_153, x_154, x_134, x_134, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_152);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_135, 1);
lean_inc(x_156);
lean_dec(x_135);
x_157 = lean_ctor_get(x_150, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_150, 1);
lean_inc(x_158);
lean_dec(x_150);
x_159 = l_Array_isEmpty___rarg(x_22);
if (x_159 == 0)
{
lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_box(0);
x_161 = lean_array_size(x_22);
x_162 = 0;
x_163 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
x_164 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(x_22, x_160, x_22, x_161, x_162, x_163, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_156);
lean_dec(x_22);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
if (lean_is_scalar(x_151)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_151;
}
lean_ctor_set(x_167, 0, x_165);
x_168 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_157, x_158, x_134, x_167, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_166);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_151);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_169 = lean_ctor_get(x_164, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_171 = x_164;
} else {
 lean_dec_ref(x_164);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; 
lean_dec(x_151);
lean_dec(x_22);
x_173 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_157, x_158, x_134, x_134, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_156);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_173;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_free_object(x_27);
lean_dec(x_132);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_174 = lean_ctor_get(x_135, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_135, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_176 = x_135;
} else {
 lean_dec_ref(x_135);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_27, 0);
x_179 = lean_ctor_get(x_27, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_27);
x_180 = lean_ctor_get(x_6, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_181 = x_6;
} else {
 lean_dec_ref(x_6);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_179);
x_183 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_178, x_179, x_180, x_182, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_52);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_179);
x_189 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
if (lean_is_scalar(x_24)) {
 x_190 = lean_alloc_ctor(7, 2, 0);
} else {
 x_190 = x_24;
 lean_ctor_set_tag(x_190, 7);
}
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
if (x_25 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6;
x_192 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_191, x_190);
if (lean_is_scalar(x_181)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_181;
}
lean_ctor_set(x_193, 0, x_192);
if (lean_is_scalar(x_186)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_186;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_185);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10;
x_196 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_195, x_190);
if (lean_is_scalar(x_181)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_181;
}
lean_ctor_set(x_197, 0, x_196);
if (lean_is_scalar(x_186)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_186;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_185);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_24);
x_199 = lean_ctor_get(x_184, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_200 = x_184;
} else {
 lean_dec_ref(x_184);
 x_200 = lean_box(0);
}
if (x_11 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_200);
lean_dec(x_22);
x_201 = lean_ctor_get(x_183, 1);
lean_inc(x_201);
lean_dec(x_183);
x_202 = lean_ctor_get(x_199, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 1);
lean_inc(x_203);
lean_dec(x_199);
x_204 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_202, x_203, x_182, x_182, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_201);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = lean_ctor_get(x_183, 1);
lean_inc(x_205);
lean_dec(x_183);
x_206 = lean_ctor_get(x_199, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_199, 1);
lean_inc(x_207);
lean_dec(x_199);
x_208 = l_Array_isEmpty___rarg(x_22);
if (x_208 == 0)
{
lean_object* x_209; size_t x_210; size_t x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_box(0);
x_210 = lean_array_size(x_22);
x_211 = 0;
x_212 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_4);
x_213 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(x_22, x_209, x_22, x_210, x_211, x_212, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_205);
lean_dec(x_22);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
if (lean_is_scalar(x_200)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_200;
}
lean_ctor_set(x_216, 0, x_214);
x_217 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_206, x_207, x_182, x_216, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_215);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_200);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_220 = x_213;
} else {
 lean_dec_ref(x_213);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; 
lean_dec(x_200);
lean_dec(x_22);
x_222 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_206, x_207, x_182, x_182, x_7, x_8, x_9, x_10, x_4, x_5, x_13, x_14, x_205);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_222;
}
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_223 = lean_ctor_get(x_183, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_183, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_225 = x_183;
} else {
 lean_dec_ref(x_183);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_227 = !lean_is_exclusive(x_26);
if (x_227 == 0)
{
return x_26;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_26, 0);
x_229 = lean_ctor_get(x_26, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_26);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_323; 
x_235 = lean_ctor_get(x_13, 0);
x_236 = lean_ctor_get(x_13, 1);
x_237 = lean_ctor_get(x_13, 3);
x_238 = lean_ctor_get(x_13, 5);
x_239 = lean_ctor_get(x_13, 6);
x_240 = lean_ctor_get(x_13, 7);
x_241 = lean_ctor_get(x_13, 8);
x_242 = lean_ctor_get(x_13, 9);
x_243 = lean_ctor_get(x_13, 10);
x_244 = lean_ctor_get(x_13, 11);
x_245 = lean_ctor_get_uint8(x_13, sizeof(void*)*13 + 1);
x_246 = lean_ctor_get(x_13, 12);
lean_inc(x_246);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_13);
x_247 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1;
x_248 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_247);
x_249 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_249, 0, x_235);
lean_ctor_set(x_249, 1, x_236);
lean_ctor_set(x_249, 2, x_1);
lean_ctor_set(x_249, 3, x_237);
lean_ctor_set(x_249, 4, x_248);
lean_ctor_set(x_249, 5, x_238);
lean_ctor_set(x_249, 6, x_239);
lean_ctor_set(x_249, 7, x_240);
lean_ctor_set(x_249, 8, x_241);
lean_ctor_set(x_249, 9, x_242);
lean_ctor_set(x_249, 10, x_243);
lean_ctor_set(x_249, 11, x_244);
lean_ctor_set(x_249, 12, x_246);
lean_ctor_set_uint8(x_249, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_249, sizeof(void*)*13 + 1, x_245);
lean_inc(x_3);
x_250 = l_Lean_Meta_getMVars(x_3, x_4, x_5, x_249, x_14, x_15);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
x_323 = l_Array_isEmpty___rarg(x_251);
if (x_323 == 0)
{
uint8_t x_324; 
x_324 = 1;
x_254 = x_324;
goto block_322;
}
else
{
uint8_t x_325; 
x_325 = 0;
x_254 = x_325;
goto block_322;
}
block_322:
{
lean_object* x_255; 
lean_inc(x_14);
lean_inc(x_249);
lean_inc(x_5);
lean_inc(x_4);
x_255 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax(x_3, x_254, x_4, x_5, x_249, x_14, x_252);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_249);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
x_259 = lean_ctor_get(x_256, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_260 = x_256;
} else {
 lean_dec_ref(x_256);
 x_260 = lean_box(0);
}
x_261 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
if (lean_is_scalar(x_260)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_260;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_259);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
lean_ctor_set(x_264, 2, x_263);
lean_ctor_set(x_264, 3, x_263);
lean_ctor_set(x_264, 4, x_263);
lean_ctor_set(x_264, 5, x_263);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
if (lean_is_scalar(x_258)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_258;
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_257);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_267 = lean_ctor_get(x_255, 1);
lean_inc(x_267);
lean_dec(x_255);
x_268 = lean_ctor_get(x_256, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_256, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_270 = x_256;
} else {
 lean_dec_ref(x_256);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_6, 0);
lean_inc(x_271);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_272 = x_6;
} else {
 lean_dec_ref(x_6);
 x_272 = lean_box(0);
}
x_273 = lean_box(0);
lean_inc(x_14);
lean_inc(x_249);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_269);
x_274 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_268, x_269, x_271, x_273, x_7, x_8, x_9, x_10, x_4, x_5, x_249, x_14, x_267);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_251);
lean_dec(x_249);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
x_278 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
if (lean_is_scalar(x_270)) {
 x_279 = lean_alloc_ctor(7, 2, 0);
} else {
 x_279 = x_270;
 lean_ctor_set_tag(x_279, 7);
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_269);
x_280 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
if (lean_is_scalar(x_253)) {
 x_281 = lean_alloc_ctor(7, 2, 0);
} else {
 x_281 = x_253;
 lean_ctor_set_tag(x_281, 7);
}
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
if (x_254 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6;
x_283 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_282, x_281);
if (lean_is_scalar(x_272)) {
 x_284 = lean_alloc_ctor(1, 1, 0);
} else {
 x_284 = x_272;
}
lean_ctor_set(x_284, 0, x_283);
if (lean_is_scalar(x_277)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_277;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_276);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10;
x_287 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_286, x_281);
if (lean_is_scalar(x_272)) {
 x_288 = lean_alloc_ctor(1, 1, 0);
} else {
 x_288 = x_272;
}
lean_ctor_set(x_288, 0, x_287);
if (lean_is_scalar(x_277)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_277;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_276);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_253);
x_290 = lean_ctor_get(x_275, 0);
lean_inc(x_290);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_291 = x_275;
} else {
 lean_dec_ref(x_275);
 x_291 = lean_box(0);
}
if (x_11 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_291);
lean_dec(x_251);
x_292 = lean_ctor_get(x_274, 1);
lean_inc(x_292);
lean_dec(x_274);
x_293 = lean_ctor_get(x_290, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
lean_dec(x_290);
x_295 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_293, x_294, x_273, x_273, x_7, x_8, x_9, x_10, x_4, x_5, x_249, x_14, x_292);
lean_dec(x_14);
lean_dec(x_249);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_ctor_get(x_274, 1);
lean_inc(x_296);
lean_dec(x_274);
x_297 = lean_ctor_get(x_290, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_290, 1);
lean_inc(x_298);
lean_dec(x_290);
x_299 = l_Array_isEmpty___rarg(x_251);
if (x_299 == 0)
{
lean_object* x_300; size_t x_301; size_t x_302; lean_object* x_303; lean_object* x_304; 
x_300 = lean_box(0);
x_301 = lean_array_size(x_251);
x_302 = 0;
x_303 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11;
lean_inc(x_14);
lean_inc(x_249);
lean_inc(x_5);
lean_inc(x_4);
x_304 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(x_251, x_300, x_251, x_301, x_302, x_303, x_7, x_8, x_9, x_10, x_4, x_5, x_249, x_14, x_296);
lean_dec(x_251);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
if (lean_is_scalar(x_291)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_291;
}
lean_ctor_set(x_307, 0, x_305);
x_308 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_297, x_298, x_273, x_307, x_7, x_8, x_9, x_10, x_4, x_5, x_249, x_14, x_306);
lean_dec(x_14);
lean_dec(x_249);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_291);
lean_dec(x_249);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_309 = lean_ctor_get(x_304, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_311 = x_304;
} else {
 lean_dec_ref(x_304);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; 
lean_dec(x_291);
lean_dec(x_251);
x_313 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_297, x_298, x_273, x_273, x_7, x_8, x_9, x_10, x_4, x_5, x_249, x_14, x_296);
lean_dec(x_14);
lean_dec(x_249);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_313;
}
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_272);
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_249);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_314 = lean_ctor_get(x_274, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_274, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_316 = x_274;
} else {
 lean_dec_ref(x_274);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_249);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_318 = lean_ctor_get(x_255, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_255, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_320 = x_255;
} else {
 lean_dec_ref(x_255);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_52; 
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
x_14 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___closed__1;
x_15 = 0;
x_16 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_13, x_14, x_15);
x_17 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2;
x_18 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_16, x_17);
x_19 = lean_st_ref_get(x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_52 = l_Lean_Kernel_isDiagnosticsEnabled(x_22);
lean_dec(x_22);
if (x_52 == 0)
{
if (x_18 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2(x_16, x_18, x_3, x_8, x_9, x_2, x_4, x_5, x_6, x_7, x_1, x_53, x_10, x_11, x_21);
return x_54;
}
else
{
lean_object* x_55; 
x_55 = lean_box(0);
x_23 = x_55;
goto block_51;
}
}
else
{
if (x_18 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_23 = x_56;
goto block_51;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
x_58 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2(x_16, x_18, x_3, x_8, x_9, x_2, x_4, x_5, x_6, x_7, x_1, x_57, x_10, x_11, x_21);
return x_58;
}
}
block_51:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_23);
x_24 = lean_st_ref_take(x_11, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 5);
lean_dec(x_29);
x_30 = l_Lean_Kernel_enableDiag(x_28, x_18);
x_31 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5;
lean_ctor_set(x_25, 5, x_31);
lean_ctor_set(x_25, 0, x_30);
x_32 = lean_st_ref_set(x_11, x_25, x_26);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2(x_16, x_18, x_3, x_8, x_9, x_2, x_4, x_5, x_6, x_7, x_1, x_34, x_10, x_11, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
x_38 = lean_ctor_get(x_25, 2);
x_39 = lean_ctor_get(x_25, 3);
x_40 = lean_ctor_get(x_25, 4);
x_41 = lean_ctor_get(x_25, 6);
x_42 = lean_ctor_get(x_25, 7);
x_43 = lean_ctor_get(x_25, 8);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_44 = l_Lean_Kernel_enableDiag(x_36, x_18);
x_45 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5;
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_45);
lean_ctor_set(x_46, 6, x_41);
lean_ctor_set(x_46, 7, x_42);
lean_ctor_set(x_46, 8, x_43);
x_47 = lean_st_ref_set(x_11, x_46, x_26);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2(x_16, x_18, x_3, x_8, x_9, x_2, x_4, x_5, x_6, x_7, x_1, x_49, x_10, x_11, x_48);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_11);
lean_dec(x_11);
x_18 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17, x_12, x_13, x_14, x_15);
lean_dec(x_12);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(x_4, x_6, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3;
x_22 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_20, x_3, x_21, x_5, x_12, x_13, x_14, x_15, x_19);
lean_dec(x_13);
lean_dec(x_12);
return x_22;
}
else
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
if (x_7 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic_throwExs___spec__2(x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = 0;
x_29 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_27, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(x_1, x_2, x_3, x_17, x_5, x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_4, x_3);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_uget(x_5, x_4);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_5, x_4, x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore(x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_25 = lean_array_uset(x_19, x_4, x_21);
x_4 = x_24;
x_5 = x_25;
x_14 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_push(x_3, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_6, x_5);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; 
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_array_push(x_21, x_22);
lean_ctor_set(x_7, 1, x_23);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_array_push(x_28, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = 1;
x_33 = lean_usize_add(x_6, x_32);
x_6 = x_33;
x_7 = x_31;
goto _start;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_7);
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
x_36 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___spec__2(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_41 = lean_ctor_get(x_7, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
lean_dec(x_19);
x_44 = lean_box(0);
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___lambda__1(x_43, x_42, x_41, x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 1;
x_50 = lean_usize_add(x_6, x_49);
x_6 = x_50;
x_7 = x_48;
x_16 = x_47;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_8, 6);
x_12 = lean_ctor_get(x_8, 7);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = 0;
x_16 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_17 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_4);
lean_ctor_set(x_17, 3, x_16);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 2, x_6);
x_18 = lean_st_ref_take(x_9, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 6);
x_23 = l_Lean_MessageLog_add(x_17, x_22);
lean_ctor_set(x_19, 6, x_23);
x_24 = lean_st_ref_set(x_9, x_19, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
x_33 = lean_ctor_get(x_19, 2);
x_34 = lean_ctor_get(x_19, 3);
x_35 = lean_ctor_get(x_19, 4);
x_36 = lean_ctor_get(x_19, 5);
x_37 = lean_ctor_get(x_19, 6);
x_38 = lean_ctor_get(x_19, 7);
x_39 = lean_ctor_get(x_19, 8);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_40 = l_Lean_MessageLog_add(x_17, x_37);
x_41 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_33);
lean_ctor_set(x_41, 3, x_34);
lean_ctor_set(x_41, 4, x_35);
lean_ctor_set(x_41, 5, x_36);
lean_ctor_set(x_41, 6, x_40);
lean_ctor_set(x_41, 7, x_38);
lean_ctor_set(x_41, 8, x_39);
x_42 = lean_st_ref_set(x_9, x_41, x_20);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2;
x_10 = lean_string_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_12 = lean_string_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__3;
x_15 = lean_string_dec_eq(x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__4;
x_17 = lean_string_dec_eq(x_7, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
default: 
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_189; uint8_t x_190; 
x_189 = 2;
x_190 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_189);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_box(0);
x_14 = x_191;
goto block_188;
}
else
{
lean_object* x_192; uint8_t x_193; 
lean_inc(x_2);
x_192 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_box(0);
x_14 = x_194;
goto block_188;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_11);
lean_dec(x_2);
x_195 = lean_box(0);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_13);
return x_196;
}
}
block_188:
{
uint8_t x_15; lean_object* x_182; uint8_t x_183; uint8_t x_184; 
lean_dec(x_14);
x_182 = lean_ctor_get(x_11, 2);
lean_inc(x_182);
x_183 = 1;
x_184 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_107_(x_3, x_183);
if (x_184 == 0)
{
lean_dec(x_182);
x_15 = x_3;
goto block_181;
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__2;
x_186 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_182, x_185);
lean_dec(x_182);
if (x_186 == 0)
{
x_15 = x_3;
goto block_181;
}
else
{
uint8_t x_187; 
x_187 = 2;
x_15 = x_187;
goto block_181;
}
}
block_181:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 5);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*13 + 1);
x_20 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_21 = 0;
x_22 = l_Lean_Syntax_getPos_x3f(x_20, x_21);
x_23 = l_Lean_Syntax_getTailPos_x3f(x_20, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_FileMap_toPosition(x_17, x_28);
lean_inc(x_29);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
if (x_19 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_24);
x_31 = lean_box(0);
x_32 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_26, x_16, x_29, x_30, x_15, x_4, x_31, x_11, x_12, x_27);
lean_dec(x_11);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_26);
x_34 = l_Lean_MessageData_hasTag(x_33, x_26);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_11);
x_35 = lean_box(0);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_24);
x_36 = lean_box(0);
x_37 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_26, x_16, x_29, x_30, x_15, x_4, x_36, x_11, x_12, x_27);
lean_dec(x_11);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_FileMap_toPosition(x_17, x_40);
lean_inc(x_41);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (x_19 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_box(0);
x_44 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_38, x_16, x_41, x_42, x_15, x_4, x_43, x_11, x_12, x_39);
lean_dec(x_11);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_38);
x_46 = l_Lean_MessageData_hasTag(x_45, x_38);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_11);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
x_50 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_38, x_16, x_41, x_42, x_15, x_4, x_49, x_11, x_12, x_39);
lean_dec(x_11);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_23);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_23, 0);
x_53 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_58 = l_Lean_FileMap_toPosition(x_17, x_57);
x_59 = l_Lean_FileMap_toPosition(x_17, x_52);
lean_dec(x_52);
lean_ctor_set(x_23, 0, x_59);
if (x_19 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_53);
x_60 = lean_box(0);
x_61 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_55, x_16, x_58, x_23, x_15, x_4, x_60, x_11, x_12, x_56);
lean_dec(x_11);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_55);
x_63 = l_Lean_MessageData_hasTag(x_62, x_55);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_23);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_16);
lean_dec(x_11);
x_64 = lean_box(0);
lean_ctor_set(x_53, 0, x_64);
return x_53;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_free_object(x_53);
x_65 = lean_box(0);
x_66 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_55, x_16, x_58, x_23, x_15, x_4, x_65, x_11, x_12, x_56);
lean_dec(x_11);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_69 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_70 = l_Lean_FileMap_toPosition(x_17, x_69);
x_71 = l_Lean_FileMap_toPosition(x_17, x_52);
lean_dec(x_52);
lean_ctor_set(x_23, 0, x_71);
if (x_19 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(0);
x_73 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_67, x_16, x_70, x_23, x_15, x_4, x_72, x_11, x_12, x_68);
lean_dec(x_11);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_67);
x_75 = l_Lean_MessageData_hasTag(x_74, x_67);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_23);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_16);
lean_dec(x_11);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_68);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_box(0);
x_79 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_67, x_16, x_70, x_23, x_15, x_4, x_78, x_11, x_12, x_68);
lean_dec(x_11);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_23, 0);
lean_inc(x_80);
lean_dec(x_23);
x_81 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_86 = l_Lean_FileMap_toPosition(x_17, x_85);
x_87 = l_Lean_FileMap_toPosition(x_17, x_80);
lean_dec(x_80);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
if (x_19 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_84);
x_89 = lean_box(0);
x_90 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_82, x_16, x_86, x_88, x_15, x_4, x_89, x_11, x_12, x_83);
lean_dec(x_11);
return x_90;
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_82);
x_92 = l_Lean_MessageData_hasTag(x_91, x_82);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_16);
lean_dec(x_11);
x_93 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_84;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_83);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_84);
x_95 = lean_box(0);
x_96 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_82, x_16, x_86, x_88, x_15, x_4, x_95, x_11, x_12, x_83);
lean_dec(x_11);
return x_96;
}
}
}
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_22);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_22, 0);
x_99 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = l_Lean_FileMap_toPosition(x_17, x_98);
lean_dec(x_98);
lean_inc(x_103);
lean_ctor_set(x_22, 0, x_103);
if (x_19 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_free_object(x_99);
x_104 = lean_box(0);
x_105 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_101, x_16, x_103, x_22, x_15, x_4, x_104, x_11, x_12, x_102);
lean_dec(x_11);
return x_105;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_101);
x_107 = l_Lean_MessageData_hasTag(x_106, x_101);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_22);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_16);
lean_dec(x_11);
x_108 = lean_box(0);
lean_ctor_set(x_99, 0, x_108);
return x_99;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_free_object(x_99);
x_109 = lean_box(0);
x_110 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_101, x_16, x_103, x_22, x_15, x_4, x_109, x_11, x_12, x_102);
lean_dec(x_11);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_99, 0);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_99);
x_113 = l_Lean_FileMap_toPosition(x_17, x_98);
lean_dec(x_98);
lean_inc(x_113);
lean_ctor_set(x_22, 0, x_113);
if (x_19 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_box(0);
x_115 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_111, x_16, x_113, x_22, x_15, x_4, x_114, x_11, x_12, x_112);
lean_dec(x_11);
return x_115;
}
else
{
lean_object* x_116; uint8_t x_117; 
x_116 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_111);
x_117 = l_Lean_MessageData_hasTag(x_116, x_111);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_22);
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_16);
lean_dec(x_11);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_112);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_box(0);
x_121 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_111, x_16, x_113, x_22, x_15, x_4, x_120, x_11, x_12, x_112);
lean_dec(x_11);
return x_121;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_22, 0);
lean_inc(x_122);
lean_dec(x_22);
x_123 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = l_Lean_FileMap_toPosition(x_17, x_122);
lean_dec(x_122);
lean_inc(x_127);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
if (x_19 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_126);
x_129 = lean_box(0);
x_130 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_124, x_16, x_127, x_128, x_15, x_4, x_129, x_11, x_12, x_125);
lean_dec(x_11);
return x_130;
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_124);
x_132 = l_Lean_MessageData_hasTag(x_131, x_124);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_16);
lean_dec(x_11);
x_133 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_126;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_125);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_126);
x_135 = lean_box(0);
x_136 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_124, x_16, x_127, x_128, x_15, x_4, x_135, x_11, x_12, x_125);
lean_dec(x_11);
return x_136;
}
}
}
}
else
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_22, 0);
lean_inc(x_137);
lean_dec(x_22);
x_138 = !lean_is_exclusive(x_23);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_23, 0);
x_140 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_17);
x_144 = l_Lean_FileMap_toPosition(x_17, x_137);
lean_dec(x_137);
x_145 = l_Lean_FileMap_toPosition(x_17, x_139);
lean_dec(x_139);
lean_ctor_set(x_23, 0, x_145);
if (x_19 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_free_object(x_140);
x_146 = lean_box(0);
x_147 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_142, x_16, x_144, x_23, x_15, x_4, x_146, x_11, x_12, x_143);
lean_dec(x_11);
return x_147;
}
else
{
lean_object* x_148; uint8_t x_149; 
x_148 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_142);
x_149 = l_Lean_MessageData_hasTag(x_148, x_142);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_23);
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_16);
lean_dec(x_11);
x_150 = lean_box(0);
lean_ctor_set(x_140, 0, x_150);
return x_140;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_free_object(x_140);
x_151 = lean_box(0);
x_152 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_142, x_16, x_144, x_23, x_15, x_4, x_151, x_11, x_12, x_143);
lean_dec(x_11);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_140, 0);
x_154 = lean_ctor_get(x_140, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_140);
lean_inc(x_17);
x_155 = l_Lean_FileMap_toPosition(x_17, x_137);
lean_dec(x_137);
x_156 = l_Lean_FileMap_toPosition(x_17, x_139);
lean_dec(x_139);
lean_ctor_set(x_23, 0, x_156);
if (x_19 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_box(0);
x_158 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_153, x_16, x_155, x_23, x_15, x_4, x_157, x_11, x_12, x_154);
lean_dec(x_11);
return x_158;
}
else
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_153);
x_160 = l_Lean_MessageData_hasTag(x_159, x_153);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_23);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_16);
lean_dec(x_11);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_154);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_box(0);
x_164 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_153, x_16, x_155, x_23, x_15, x_4, x_163, x_11, x_12, x_154);
lean_dec(x_11);
return x_164;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_23, 0);
lean_inc(x_165);
lean_dec(x_23);
x_166 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_9, x_10, x_11, x_12, x_13);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
lean_inc(x_17);
x_170 = l_Lean_FileMap_toPosition(x_17, x_137);
lean_dec(x_137);
x_171 = l_Lean_FileMap_toPosition(x_17, x_165);
lean_dec(x_165);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
if (x_19 == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_169);
x_173 = lean_box(0);
x_174 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_167, x_16, x_170, x_172, x_15, x_4, x_173, x_11, x_12, x_168);
lean_dec(x_11);
return x_174;
}
else
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1;
lean_inc(x_167);
x_176 = l_Lean_MessageData_hasTag(x_175, x_167);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_172);
lean_dec(x_170);
lean_dec(x_167);
lean_dec(x_16);
lean_dec(x_11);
x_177 = lean_box(0);
if (lean_is_scalar(x_169)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_169;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_168);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_169);
x_179 = lean_box(0);
x_180 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_167, x_16, x_170, x_172, x_15, x_4, x_179, x_11, x_12, x_168);
lean_dec(x_11);
return x_180;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 5);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4(x_12, x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_dec(x_6);
x_18 = lean_array_uget(x_3, x_5);
x_19 = 0;
lean_inc(x_13);
x_20 = l_Lean_log___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__3(x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_24 = lean_box(0);
x_5 = x_23;
x_6 = x_24;
x_15 = x_21;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try these:", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_array_size(x_2);
x_18 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__1(x_4, x_6, x_17, x_18, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_array_size(x_20);
x_24 = l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1;
x_25 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2(x_7, x_20, x_22, x_20, x_23, x_18, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2;
lean_inc(x_15);
lean_inc(x_14);
x_32 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_29, x_3, x_31, x_30, x_5, x_12, x_13, x_14, x_15, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; size_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_size(x_28);
x_35 = lean_box(0);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__5(x_28, x_22, x_28, x_34, x_18, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_33);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_28);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_25);
if (x_45 == 0)
{
return x_25;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_25, 0);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_25);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
return x_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__1(x_15, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__2(x_17, x_2, x_3, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_log___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__5(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addExactSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(x_1, x_2, x_3, x_17, x_5, x_6, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addTermSuggestions___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addTermSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_array_size(x_2);
x_12 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addTermSuggestions___spec__1(x_11, x_12, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_1, x_14, x_3, x_4, x_16, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addTermSuggestions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addTermSuggestions___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 1);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_16, x_2, x_3, x_4, x_5, x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_18);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticLet_", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letDecl", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("letIdDecl", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":=", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("let ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticHave_", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__18;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("have", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("haveDecl", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__21;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("haveIdDecl", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__23;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("haveId", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__25;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hygieneInfo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__27;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__30;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__32;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__34;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__35;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__37;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__39;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__41;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Server", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RequestM", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__43;
x_3 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__44;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__45;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__43;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__47;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__49;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__42;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__51;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__52;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__50;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__53;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__54;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__55;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__56;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__57;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__58;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__59;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__48;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__60;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__48;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__61;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__46;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__62;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__46;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__63;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__42;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__64;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__65;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__66;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__67;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__68;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__69;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__70;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__71;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__72;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__73;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__74;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__75;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__76;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__31;
x_2 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__77;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__79() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("have := ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__80() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__79;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__81() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("have ", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__81;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeSpec", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5;
x_4 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__83;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__86() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__86;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__88() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("have : ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__88;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__1;
if (lean_obj_tag(x_2) == 0)
{
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_73; 
x_73 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__17;
x_14 = x_73;
goto block_72;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_4, 0);
lean_inc(x_74);
lean_dec(x_4);
x_14 = x_74;
goto block_72;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_7, 5);
lean_inc(x_75);
x_76 = 0;
x_77 = l_Lean_SourceInfo_fromRef(x_75, x_76);
lean_dec(x_75);
x_78 = lean_ctor_get(x_7, 10);
lean_inc(x_78);
x_79 = lean_st_ref_get(x_8, x_12);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Environment_mainModule(x_83);
lean_dec(x_83);
x_85 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_77);
lean_ctor_set_tag(x_79, 2);
lean_ctor_set(x_79, 1, x_85);
lean_ctor_set(x_79, 0, x_77);
x_86 = lean_box(0);
x_87 = l_Lean_addMacroScope(x_84, x_86, x_78);
x_88 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29;
x_89 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78;
lean_inc(x_77);
x_90 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_90, 0, x_77);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_90, 2, x_87);
lean_ctor_set(x_90, 3, x_89);
x_91 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28;
lean_inc(x_77);
x_92 = l_Lean_Syntax_node1(x_77, x_91, x_90);
x_93 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_77);
x_94 = l_Lean_Syntax_node1(x_77, x_93, x_92);
x_95 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_96 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_77);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_96);
x_98 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_77);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_77);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_97);
lean_inc(x_77);
x_101 = l_Lean_Syntax_node5(x_77, x_100, x_94, x_97, x_97, x_99, x_11);
x_102 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_77);
x_103 = l_Lean_Syntax_node1(x_77, x_102, x_101);
x_104 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_105 = l_Lean_Syntax_node2(x_77, x_104, x_79, x_103);
x_106 = l_Lean_MessageData_ofExpr(x_1);
x_107 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__80;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_apply_6(x_13, x_111, x_5, x_6, x_7, x_8, x_82);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_113 = lean_ctor_get(x_79, 0);
x_114 = lean_ctor_get(x_79, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_79);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lean_Environment_mainModule(x_115);
lean_dec(x_115);
x_117 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_77);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_77);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_box(0);
x_120 = l_Lean_addMacroScope(x_116, x_119, x_78);
x_121 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29;
x_122 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78;
lean_inc(x_77);
x_123 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_123, 0, x_77);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_120);
lean_ctor_set(x_123, 3, x_122);
x_124 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28;
lean_inc(x_77);
x_125 = l_Lean_Syntax_node1(x_77, x_124, x_123);
x_126 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_77);
x_127 = l_Lean_Syntax_node1(x_77, x_126, x_125);
x_128 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_129 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_77);
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_77);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_129);
x_131 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_77);
x_132 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_132, 0, x_77);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_130);
lean_inc(x_77);
x_134 = l_Lean_Syntax_node5(x_77, x_133, x_127, x_130, x_130, x_132, x_11);
x_135 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_77);
x_136 = l_Lean_Syntax_node1(x_77, x_135, x_134);
x_137 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_138 = l_Lean_Syntax_node2(x_77, x_137, x_118, x_136);
x_139 = l_Lean_MessageData_ofExpr(x_1);
x_140 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__80;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_138);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_apply_6(x_13, x_144, x_5, x_6, x_7, x_8, x_114);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_146 = lean_ctor_get(x_4, 0);
lean_inc(x_146);
lean_dec(x_4);
x_147 = lean_ctor_get(x_7, 5);
lean_inc(x_147);
x_148 = 0;
x_149 = l_Lean_SourceInfo_fromRef(x_147, x_148);
lean_dec(x_147);
x_150 = lean_st_ref_get(x_8, x_12);
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_152 = lean_ctor_get(x_150, 1);
x_153 = lean_ctor_get(x_150, 0);
lean_dec(x_153);
x_154 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_149);
lean_ctor_set_tag(x_150, 2);
lean_ctor_set(x_150, 1, x_154);
lean_ctor_set(x_150, 0, x_149);
lean_inc(x_146);
x_155 = lean_mk_syntax_ident(x_146);
x_156 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_149);
x_157 = l_Lean_Syntax_node1(x_149, x_156, x_155);
x_158 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_159 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_149);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_149);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set(x_160, 2, x_159);
x_161 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_149);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_149);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_160);
lean_inc(x_149);
x_164 = l_Lean_Syntax_node5(x_149, x_163, x_157, x_160, x_160, x_162, x_11);
x_165 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_149);
x_166 = l_Lean_Syntax_node1(x_149, x_165, x_164);
x_167 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_168 = l_Lean_Syntax_node2(x_149, x_167, x_150, x_166);
x_169 = l_Lean_MessageData_ofName(x_146);
x_170 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82;
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_MessageData_ofExpr(x_1);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_apply_6(x_13, x_178, x_5, x_6, x_7, x_8, x_152);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_180 = lean_ctor_get(x_150, 1);
lean_inc(x_180);
lean_dec(x_150);
x_181 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_149);
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_149);
lean_ctor_set(x_182, 1, x_181);
lean_inc(x_146);
x_183 = lean_mk_syntax_ident(x_146);
x_184 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_149);
x_185 = l_Lean_Syntax_node1(x_149, x_184, x_183);
x_186 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_187 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_149);
x_188 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_188, 0, x_149);
lean_ctor_set(x_188, 1, x_186);
lean_ctor_set(x_188, 2, x_187);
x_189 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_149);
x_190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_190, 0, x_149);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_188);
lean_inc(x_149);
x_192 = l_Lean_Syntax_node5(x_149, x_191, x_185, x_188, x_188, x_190, x_11);
x_193 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_149);
x_194 = l_Lean_Syntax_node1(x_149, x_193, x_192);
x_195 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_196 = l_Lean_Syntax_node2(x_149, x_195, x_182, x_194);
x_197 = l_Lean_MessageData_ofName(x_146);
x_198 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82;
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_MessageData_ofExpr(x_1);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_205 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_196);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_apply_6(x_13, x_206, x_5, x_6, x_7, x_8, x_180);
return x_207;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_2, 0);
lean_inc(x_208);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_208);
x_209 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_208, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_289; 
x_289 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__17;
x_212 = x_289;
goto block_288;
}
else
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_4, 0);
lean_inc(x_290);
lean_dec(x_4);
x_212 = x_290;
goto block_288;
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_291 = lean_ctor_get(x_7, 5);
lean_inc(x_291);
x_292 = 0;
x_293 = l_Lean_SourceInfo_fromRef(x_291, x_292);
lean_dec(x_291);
x_294 = lean_ctor_get(x_7, 10);
lean_inc(x_294);
x_295 = lean_st_ref_get(x_8, x_211);
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_297 = lean_ctor_get(x_295, 0);
x_298 = lean_ctor_get(x_295, 1);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
x_300 = l_Lean_Environment_mainModule(x_299);
lean_dec(x_299);
x_301 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_293);
lean_ctor_set_tag(x_295, 2);
lean_ctor_set(x_295, 1, x_301);
lean_ctor_set(x_295, 0, x_293);
x_302 = lean_box(0);
x_303 = l_Lean_addMacroScope(x_300, x_302, x_294);
x_304 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29;
x_305 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78;
lean_inc(x_293);
x_306 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_306, 0, x_293);
lean_ctor_set(x_306, 1, x_304);
lean_ctor_set(x_306, 2, x_303);
lean_ctor_set(x_306, 3, x_305);
x_307 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28;
lean_inc(x_293);
x_308 = l_Lean_Syntax_node1(x_293, x_307, x_306);
x_309 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_293);
x_310 = l_Lean_Syntax_node1(x_293, x_309, x_308);
x_311 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_312 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_293);
x_313 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_313, 0, x_293);
lean_ctor_set(x_313, 1, x_311);
lean_ctor_set(x_313, 2, x_312);
x_314 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85;
lean_inc(x_293);
x_315 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_315, 0, x_293);
lean_ctor_set(x_315, 1, x_314);
x_316 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84;
lean_inc(x_293);
x_317 = l_Lean_Syntax_node2(x_293, x_316, x_315, x_210);
lean_inc(x_293);
x_318 = l_Lean_Syntax_node1(x_293, x_311, x_317);
x_319 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_293);
x_320 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_320, 0, x_293);
lean_ctor_set(x_320, 1, x_319);
x_321 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_293);
x_322 = l_Lean_Syntax_node5(x_293, x_321, x_310, x_313, x_318, x_320, x_11);
x_323 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_293);
x_324 = l_Lean_Syntax_node1(x_293, x_323, x_322);
x_325 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_326 = l_Lean_Syntax_node2(x_293, x_325, x_295, x_324);
x_327 = l_Lean_MessageData_ofExpr(x_208);
x_328 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__89;
x_329 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
x_330 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_331 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_MessageData_ofExpr(x_1);
x_333 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_335 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_326);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_apply_6(x_13, x_336, x_5, x_6, x_7, x_8, x_298);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_338 = lean_ctor_get(x_295, 0);
x_339 = lean_ctor_get(x_295, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_295);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Lean_Environment_mainModule(x_340);
lean_dec(x_340);
x_342 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_293);
x_343 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_343, 0, x_293);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_box(0);
x_345 = l_Lean_addMacroScope(x_341, x_344, x_294);
x_346 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29;
x_347 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78;
lean_inc(x_293);
x_348 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_348, 0, x_293);
lean_ctor_set(x_348, 1, x_346);
lean_ctor_set(x_348, 2, x_345);
lean_ctor_set(x_348, 3, x_347);
x_349 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28;
lean_inc(x_293);
x_350 = l_Lean_Syntax_node1(x_293, x_349, x_348);
x_351 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_293);
x_352 = l_Lean_Syntax_node1(x_293, x_351, x_350);
x_353 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_354 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_293);
x_355 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_355, 0, x_293);
lean_ctor_set(x_355, 1, x_353);
lean_ctor_set(x_355, 2, x_354);
x_356 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85;
lean_inc(x_293);
x_357 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_357, 0, x_293);
lean_ctor_set(x_357, 1, x_356);
x_358 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84;
lean_inc(x_293);
x_359 = l_Lean_Syntax_node2(x_293, x_358, x_357, x_210);
lean_inc(x_293);
x_360 = l_Lean_Syntax_node1(x_293, x_353, x_359);
x_361 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_293);
x_362 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_362, 0, x_293);
lean_ctor_set(x_362, 1, x_361);
x_363 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_293);
x_364 = l_Lean_Syntax_node5(x_293, x_363, x_352, x_355, x_360, x_362, x_11);
x_365 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_293);
x_366 = l_Lean_Syntax_node1(x_293, x_365, x_364);
x_367 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_368 = l_Lean_Syntax_node2(x_293, x_367, x_343, x_366);
x_369 = l_Lean_MessageData_ofExpr(x_208);
x_370 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__89;
x_371 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
x_372 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_373 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_374 = l_Lean_MessageData_ofExpr(x_1);
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_377 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_368);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_apply_6(x_13, x_378, x_5, x_6, x_7, x_8, x_339);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_380 = lean_ctor_get(x_4, 0);
lean_inc(x_380);
lean_dec(x_4);
x_381 = lean_ctor_get(x_7, 5);
lean_inc(x_381);
x_382 = 0;
x_383 = l_Lean_SourceInfo_fromRef(x_381, x_382);
lean_dec(x_381);
x_384 = lean_st_ref_get(x_8, x_211);
x_385 = !lean_is_exclusive(x_384);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_386 = lean_ctor_get(x_384, 1);
x_387 = lean_ctor_get(x_384, 0);
lean_dec(x_387);
x_388 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_383);
lean_ctor_set_tag(x_384, 2);
lean_ctor_set(x_384, 1, x_388);
lean_ctor_set(x_384, 0, x_383);
lean_inc(x_380);
x_389 = lean_mk_syntax_ident(x_380);
x_390 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_383);
x_391 = l_Lean_Syntax_node1(x_383, x_390, x_389);
x_392 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_393 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_383);
x_394 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_394, 0, x_383);
lean_ctor_set(x_394, 1, x_392);
lean_ctor_set(x_394, 2, x_393);
x_395 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85;
lean_inc(x_383);
x_396 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_396, 0, x_383);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84;
lean_inc(x_383);
x_398 = l_Lean_Syntax_node2(x_383, x_397, x_396, x_210);
lean_inc(x_383);
x_399 = l_Lean_Syntax_node1(x_383, x_392, x_398);
x_400 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_383);
x_401 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_401, 0, x_383);
lean_ctor_set(x_401, 1, x_400);
x_402 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_383);
x_403 = l_Lean_Syntax_node5(x_383, x_402, x_391, x_394, x_399, x_401, x_11);
x_404 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_383);
x_405 = l_Lean_Syntax_node1(x_383, x_404, x_403);
x_406 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_407 = l_Lean_Syntax_node2(x_383, x_406, x_384, x_405);
x_408 = l_Lean_MessageData_ofName(x_380);
x_409 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82;
x_410 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
x_411 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87;
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_MessageData_ofExpr(x_208);
x_414 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
x_415 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_416 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_417 = l_Lean_MessageData_ofExpr(x_1);
x_418 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_420 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_407);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_apply_6(x_13, x_421, x_5, x_6, x_7, x_8, x_386);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_423 = lean_ctor_get(x_384, 1);
lean_inc(x_423);
lean_dec(x_384);
x_424 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20;
lean_inc(x_383);
x_425 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_425, 0, x_383);
lean_ctor_set(x_425, 1, x_424);
lean_inc(x_380);
x_426 = lean_mk_syntax_ident(x_380);
x_427 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26;
lean_inc(x_383);
x_428 = l_Lean_Syntax_node1(x_383, x_427, x_426);
x_429 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_430 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_383);
x_431 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_431, 0, x_383);
lean_ctor_set(x_431, 1, x_429);
lean_ctor_set(x_431, 2, x_430);
x_432 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85;
lean_inc(x_383);
x_433 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_433, 0, x_383);
lean_ctor_set(x_433, 1, x_432);
x_434 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84;
lean_inc(x_383);
x_435 = l_Lean_Syntax_node2(x_383, x_434, x_433, x_210);
lean_inc(x_383);
x_436 = l_Lean_Syntax_node1(x_383, x_429, x_435);
x_437 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_383);
x_438 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_438, 0, x_383);
lean_ctor_set(x_438, 1, x_437);
x_439 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24;
lean_inc(x_383);
x_440 = l_Lean_Syntax_node5(x_383, x_439, x_428, x_431, x_436, x_438, x_11);
x_441 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22;
lean_inc(x_383);
x_442 = l_Lean_Syntax_node1(x_383, x_441, x_440);
x_443 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19;
x_444 = l_Lean_Syntax_node2(x_383, x_443, x_425, x_442);
x_445 = l_Lean_MessageData_ofName(x_380);
x_446 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82;
x_447 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_445);
x_448 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87;
x_449 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
x_450 = l_Lean_MessageData_ofExpr(x_208);
x_451 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
x_452 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_453 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
x_454 = l_Lean_MessageData_ofExpr(x_1);
x_455 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
x_456 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_457 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_444);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_apply_6(x_13, x_458, x_5, x_6, x_7, x_8, x_423);
return x_459;
}
}
}
block_288:
{
lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_213 = lean_ctor_get(x_7, 5);
lean_inc(x_213);
x_214 = 0;
x_215 = l_Lean_SourceInfo_fromRef(x_213, x_214);
lean_dec(x_213);
x_216 = lean_st_ref_get(x_8, x_211);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_218 = lean_ctor_get(x_216, 1);
x_219 = lean_ctor_get(x_216, 0);
lean_dec(x_219);
x_220 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4;
lean_inc(x_215);
lean_ctor_set_tag(x_216, 2);
lean_ctor_set(x_216, 1, x_220);
lean_ctor_set(x_216, 0, x_215);
lean_inc(x_212);
x_221 = lean_mk_syntax_ident(x_212);
x_222 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_223 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_215);
x_224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_224, 0, x_215);
lean_ctor_set(x_224, 1, x_222);
lean_ctor_set(x_224, 2, x_223);
x_225 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85;
lean_inc(x_215);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_215);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84;
lean_inc(x_215);
x_228 = l_Lean_Syntax_node2(x_215, x_227, x_226, x_210);
lean_inc(x_215);
x_229 = l_Lean_Syntax_node1(x_215, x_222, x_228);
x_230 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_215);
x_231 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_231, 0, x_215);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9;
lean_inc(x_215);
x_233 = l_Lean_Syntax_node5(x_215, x_232, x_221, x_224, x_229, x_231, x_11);
x_234 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7;
lean_inc(x_215);
x_235 = l_Lean_Syntax_node1(x_215, x_234, x_233);
x_236 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3;
x_237 = l_Lean_Syntax_node2(x_215, x_236, x_216, x_235);
x_238 = l_Lean_MessageData_ofName(x_212);
x_239 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13;
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
x_241 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87;
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_MessageData_ofExpr(x_208);
x_244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_MessageData_ofExpr(x_1);
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_237);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_apply_6(x_13, x_251, x_5, x_6, x_7, x_8, x_218);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_253 = lean_ctor_get(x_216, 1);
lean_inc(x_253);
lean_dec(x_216);
x_254 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4;
lean_inc(x_215);
x_255 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_255, 0, x_215);
lean_ctor_set(x_255, 1, x_254);
lean_inc(x_212);
x_256 = lean_mk_syntax_ident(x_212);
x_257 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_258 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_215);
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_215);
lean_ctor_set(x_259, 1, x_257);
lean_ctor_set(x_259, 2, x_258);
x_260 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85;
lean_inc(x_215);
x_261 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_261, 0, x_215);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84;
lean_inc(x_215);
x_263 = l_Lean_Syntax_node2(x_215, x_262, x_261, x_210);
lean_inc(x_215);
x_264 = l_Lean_Syntax_node1(x_215, x_257, x_263);
x_265 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_215);
x_266 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_266, 0, x_215);
lean_ctor_set(x_266, 1, x_265);
x_267 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9;
lean_inc(x_215);
x_268 = l_Lean_Syntax_node5(x_215, x_267, x_256, x_259, x_264, x_266, x_11);
x_269 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7;
lean_inc(x_215);
x_270 = l_Lean_Syntax_node1(x_215, x_269, x_268);
x_271 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3;
x_272 = l_Lean_Syntax_node2(x_215, x_271, x_255, x_270);
x_273 = l_Lean_MessageData_ofName(x_212);
x_274 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13;
x_275 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87;
x_277 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = l_Lean_MessageData_ofExpr(x_208);
x_279 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_281 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = l_Lean_MessageData_ofExpr(x_1);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
x_284 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_272);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_apply_6(x_13, x_286, x_5, x_6, x_7, x_8, x_253);
return x_287;
}
}
}
else
{
uint8_t x_460; 
lean_dec(x_208);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_460 = !lean_is_exclusive(x_209);
if (x_460 == 0)
{
return x_209;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_209, 0);
x_462 = lean_ctor_get(x_209, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_209);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
}
block_72:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
x_16 = 0;
x_17 = l_Lean_SourceInfo_fromRef(x_15, x_16);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_8, x_12);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4;
lean_inc(x_17);
lean_ctor_set_tag(x_18, 2);
lean_ctor_set(x_18, 1, x_22);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_14);
x_23 = lean_mk_syntax_ident(x_14);
x_24 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_25 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_17);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_17);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9;
lean_inc(x_26);
lean_inc(x_17);
x_30 = l_Lean_Syntax_node5(x_17, x_29, x_23, x_26, x_26, x_28, x_11);
x_31 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7;
lean_inc(x_17);
x_32 = l_Lean_Syntax_node1(x_17, x_31, x_30);
x_33 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3;
x_34 = l_Lean_Syntax_node2(x_17, x_33, x_18, x_32);
x_35 = l_Lean_MessageData_ofName(x_14);
x_36 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_MessageData_ofExpr(x_1);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_apply_6(x_13, x_44, x_5, x_6, x_7, x_8, x_20);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_dec(x_18);
x_47 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4;
lean_inc(x_17);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_14);
x_49 = lean_mk_syntax_ident(x_14);
x_50 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_51 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_17);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_51);
x_53 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11;
lean_inc(x_17);
x_54 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9;
lean_inc(x_52);
lean_inc(x_17);
x_56 = l_Lean_Syntax_node5(x_17, x_55, x_49, x_52, x_52, x_54, x_11);
x_57 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7;
lean_inc(x_17);
x_58 = l_Lean_Syntax_node1(x_17, x_57, x_56);
x_59 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3;
x_60 = l_Lean_Syntax_node2(x_17, x_59, x_48, x_58);
x_61 = l_Lean_MessageData_ofName(x_14);
x_62 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_MessageData_ofExpr(x_1);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_60);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_apply_6(x_13, x_70, x_5, x_6, x_7, x_8, x_46);
return x_71;
}
}
}
else
{
uint8_t x_464; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_464 = !lean_is_exclusive(x_10);
if (x_464 == 0)
{
return x_10;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_10, 0);
x_466 = lean_ctor_get(x_10, 1);
lean_inc(x_466);
lean_inc(x_465);
lean_dec(x_10);
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
return x_467;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_3);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_17);
x_20 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3;
x_21 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_1, x_19, x_2, x_20, x_17, x_10, x_11, x_12, x_13, x_14);
return x_21;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a proof", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
x_16 = lean_infer_type(x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_19 = l_Lean_Meta_isProp(x_17, x_11, x_12, x_13, x_14, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___boxed), 9, 4);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_20);
lean_closure_set(x_22, 3, x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_23 = l_Lean_Meta_withExposedNames___rarg(x_22, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__3(x_1, x_5, x_27, x_26, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_6, 0);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_35 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_31, x_32, x_33, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_5);
lean_dec(x_1);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__3;
x_39 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_38, x_32);
x_40 = 0;
x_41 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_39, x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_32);
x_48 = lean_ctor_get(x_36, 0);
lean_inc(x_48);
lean_dec(x_36);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_dec(x_35);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_box(0);
x_53 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__3(x_1, x_5, x_51, x_50, x_52, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_49);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_32);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_35);
if (x_54 == 0)
{
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_35, 0);
x_56 = lean_ctor_get(x_35, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_35);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_23);
if (x_58 == 0)
{
return x_23;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_23, 0);
x_60 = lean_ctor_get(x_23, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_23);
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
lean_dec(x_14);
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
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
return x_19;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_19, 0);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_19);
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
lean_dec(x_14);
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
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_16);
if (x_66 == 0)
{
return x_16;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_16, 0);
x_68 = lean_ctor_get(x_16, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_16);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwRule", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("patternIgnore", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("token", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("← ", 4, 2);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__5;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("←", 3, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax(x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = lean_unbox(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_6, 5);
lean_inc(x_20);
x_21 = 0;
x_22 = l_Lean_SourceInfo_fromRef(x_20, x_21);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_7, x_19);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_26 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_22);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2;
x_29 = l_Lean_Syntax_node2(x_22, x_28, x_27, x_18);
x_30 = 1;
x_31 = lean_usize_add(x_2, x_30);
x_32 = lean_array_uset(x_13, x_2, x_29);
x_2 = x_31;
x_3 = x_32;
x_8 = x_24;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_ctor_get(x_6, 5);
lean_inc(x_36);
x_37 = 0;
x_38 = l_Lean_SourceInfo_fromRef(x_36, x_37);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_7, x_35);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_39, 1);
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__8;
lean_inc(x_38);
lean_ctor_set_tag(x_39, 2);
lean_ctor_set(x_39, 1, x_43);
lean_ctor_set(x_39, 0, x_38);
x_44 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__7;
lean_inc(x_38);
x_45 = l_Lean_Syntax_node1(x_38, x_44, x_39);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__4;
lean_inc(x_38);
x_47 = l_Lean_Syntax_node1(x_38, x_46, x_45);
x_48 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_38);
x_49 = l_Lean_Syntax_node1(x_38, x_48, x_47);
x_50 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2;
x_51 = l_Lean_Syntax_node2(x_38, x_50, x_49, x_34);
x_52 = 1;
x_53 = lean_usize_add(x_2, x_52);
x_54 = lean_array_uset(x_13, x_2, x_51);
x_2 = x_53;
x_3 = x_54;
x_8 = x_41;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_39, 1);
lean_inc(x_56);
lean_dec(x_39);
x_57 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__8;
lean_inc(x_38);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__7;
lean_inc(x_38);
x_60 = l_Lean_Syntax_node1(x_38, x_59, x_58);
x_61 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__4;
lean_inc(x_38);
x_62 = l_Lean_Syntax_node1(x_38, x_61, x_60);
x_63 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_38);
x_64 = l_Lean_Syntax_node1(x_38, x_63, x_62);
x_65 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2;
x_66 = l_Lean_Syntax_node2(x_38, x_65, x_64, x_34);
x_67 = 1;
x_68 = lean_usize_add(x_2, x_67);
x_69 = lean_array_uset(x_13, x_2, x_66);
x_2 = x_68;
x_3 = x_69;
x_8 = x_56;
goto _start;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_16);
if (x_71 == 0)
{
return x_16;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_16, 0);
x_73 = lean_ctor_get(x_16, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_16);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = l_Lean_Expr_isConst(x_8);
x_11 = lean_unbox(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_MessageData_ofExpr(x_8);
x_13 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_12);
lean_ctor_set(x_5, 0, x_13);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_MessageData_ofConst(x_8);
x_16 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_15);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
if (x_10 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_MessageData_ofExpr(x_8);
x_19 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_19);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_MessageData_ofConst(x_8);
x_22 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4;
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_22);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = l_Lean_Expr_isConst(x_25);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
if (x_28 == 0)
{
if (x_27 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_MessageData_ofExpr(x_25);
x_30 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_31);
{
lean_object* _tmp_0 = x_24;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_MessageData_ofConst(x_25);
x_34 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_35);
{
lean_object* _tmp_0 = x_24;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
if (x_27 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_MessageData_ofExpr(x_25);
x_38 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_39);
{
lean_object* _tmp_0 = x_24;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = l_Lean_MessageData_ofConst(x_25);
x_42 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_43);
{
lean_object* _tmp_0 = x_24;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Expr_isConst(x_47);
x_51 = lean_unbox(x_48);
lean_dec(x_48);
if (x_51 == 0)
{
if (x_50 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Lean_MessageData_ofExpr(x_47);
x_53 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2;
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(7, 2, 0);
} else {
 x_54 = x_49;
 lean_ctor_set_tag(x_54, 7);
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_2);
x_1 = x_46;
x_2 = x_55;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = l_Lean_MessageData_ofConst(x_47);
x_58 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2;
if (lean_is_scalar(x_49)) {
 x_59 = lean_alloc_ctor(7, 2, 0);
} else {
 x_59 = x_49;
 lean_ctor_set_tag(x_59, 7);
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_2);
x_1 = x_46;
x_2 = x_60;
goto _start;
}
}
else
{
if (x_50 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l_Lean_MessageData_ofExpr(x_47);
x_63 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4;
if (lean_is_scalar(x_49)) {
 x_64 = lean_alloc_ctor(7, 2, 0);
} else {
 x_64 = x_49;
 lean_ctor_set_tag(x_64, 7);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_2);
x_1 = x_46;
x_2 = x_65;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = l_Lean_MessageData_ofConst(x_47);
x_68 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4;
if (lean_is_scalar(x_49)) {
 x_69 = lean_alloc_ctor(7, 2, 0);
} else {
 x_69 = x_49;
 lean_ctor_set_tag(x_69, 7);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_2);
x_1 = x_46;
x_2 = x_70;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n-- no goals", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__8;
x_2 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n-- ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_2 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rw ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" at ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwSeq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__17;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rw", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__20;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwRuleSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__22;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("location", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__25;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("at", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("locationHyp", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1;
x_2 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1;
x_3 = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3;
x_4 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__28;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_124; lean_object* x_125; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__1;
x_16 = l_Lean_Syntax_SepArray_ofElems(x_15, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_184; 
x_184 = lean_box(0);
x_124 = x_184;
x_125 = x_14;
goto block_183;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_6, 0);
lean_inc(x_185);
x_186 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_187 = l_Lean_PrettyPrinter_delab(x_185, x_186, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_9, 5);
lean_inc(x_190);
x_191 = 0;
x_192 = l_Lean_SourceInfo_fromRef(x_190, x_191);
lean_dec(x_190);
x_193 = lean_st_ref_get(x_10, x_189);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_195 = lean_ctor_get(x_193, 1);
x_196 = lean_ctor_get(x_193, 0);
lean_dec(x_196);
x_197 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__27;
lean_inc(x_192);
lean_ctor_set_tag(x_193, 2);
lean_ctor_set(x_193, 1, x_197);
lean_ctor_set(x_193, 0, x_192);
x_198 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_192);
x_199 = l_Lean_Syntax_node1(x_192, x_198, x_188);
x_200 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__29;
lean_inc(x_192);
x_201 = l_Lean_Syntax_node1(x_192, x_200, x_199);
x_202 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__26;
x_203 = l_Lean_Syntax_node2(x_192, x_202, x_193, x_201);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_124 = x_204;
x_125 = x_195;
goto block_183;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_205 = lean_ctor_get(x_193, 1);
lean_inc(x_205);
lean_dec(x_193);
x_206 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__27;
lean_inc(x_192);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_192);
lean_ctor_set(x_207, 1, x_206);
x_208 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
lean_inc(x_192);
x_209 = l_Lean_Syntax_node1(x_192, x_208, x_188);
x_210 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__29;
lean_inc(x_192);
x_211 = l_Lean_Syntax_node1(x_192, x_210, x_209);
x_212 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__26;
x_213 = l_Lean_Syntax_node2(x_192, x_212, x_207, x_211);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_124 = x_214;
x_125 = x_205;
goto block_183;
}
}
else
{
uint8_t x_215; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_215 = !lean_is_exclusive(x_187);
if (x_215 == 0)
{
return x_187;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_187, 0);
x_217 = lean_ctor_get(x_187, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_187);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
block_123:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_box(0);
x_20 = l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2(x_4, x_19);
x_21 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__4;
x_22 = l_Lean_MessageData_joinSep(x_20, x_21);
x_23 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5;
x_24 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6;
x_25 = l_Lean_MessageData_bracket(x_23, x_22, x_24);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__14;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_25);
x_112 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_26 = x_113;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_6, 0);
lean_inc(x_114);
lean_dec(x_6);
x_115 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__14;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_25);
x_117 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__16;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_MessageData_ofExpr(x_114);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_26 = x_122;
goto block_109;
}
block_109:
{
lean_object* x_27; 
x_27 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_26, x_7, x_8, x_9, x_10, x_18);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__9;
x_31 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(x_28, x_17, x_30, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_31;
}
case 1:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
lean_inc(x_35);
x_36 = l_Lean_MessageData_ofExpr(x_35);
x_37 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__11;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_37);
x_38 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_39, x_7, x_8, x_9, x_10, x_34);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_44 = l_Lean_PrettyPrinter_ppExpr(x_35, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Std_Format_defWidth;
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_format_pretty(x_45, x_47, x_48, x_48);
x_50 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10;
x_51 = lean_string_append(x_50, x_49);
lean_dec(x_49);
x_52 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_53 = lean_string_append(x_51, x_52);
lean_ctor_set(x_40, 1, x_53);
x_54 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(x_33, x_17, x_40, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_54;
}
else
{
uint8_t x_55; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_55 = !lean_is_exclusive(x_44);
if (x_55 == 0)
{
return x_44;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_44, 0);
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_44);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_40, 0);
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_40);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_61 = l_Lean_PrettyPrinter_ppExpr(x_35, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Std_Format_defWidth;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_format_pretty(x_62, x_64, x_65, x_65);
x_67 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10;
x_68 = lean_string_append(x_67, x_66);
lean_dec(x_66);
x_69 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_59);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(x_33, x_17, x_71, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_59);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
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
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_77 = lean_ctor_get(x_27, 0);
x_78 = lean_ctor_get(x_27, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_27);
x_79 = lean_ctor_get(x_5, 0);
lean_inc(x_79);
lean_dec(x_5);
lean_inc(x_79);
x_80 = l_Lean_MessageData_ofExpr(x_79);
x_81 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__11;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_84, x_7, x_8, x_9, x_10, x_78);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_89 = l_Lean_PrettyPrinter_ppExpr(x_79, x_7, x_8, x_9, x_10, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Std_Format_defWidth;
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_format_pretty(x_90, x_92, x_93, x_93);
x_95 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10;
x_96 = lean_string_append(x_95, x_94);
lean_dec(x_94);
x_97 = l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1;
x_98 = lean_string_append(x_96, x_97);
if (lean_is_scalar(x_88)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_88;
}
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(x_77, x_17, x_99, x_7, x_8, x_9, x_10, x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_77);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_101 = lean_ctor_get(x_89, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_89, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_103 = x_89;
} else {
 lean_dec_ref(x_89);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
}
default: 
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_27, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_27, 1);
lean_inc(x_106);
lean_dec(x_27);
x_107 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__12;
x_108 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(x_105, x_17, x_107, x_7, x_8, x_9, x_10, x_106);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_108;
}
}
}
}
block_183:
{
lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_126 = lean_ctor_get(x_9, 5);
lean_inc(x_126);
x_127 = 0;
x_128 = l_Lean_SourceInfo_fromRef(x_126, x_127);
lean_dec(x_126);
x_129 = lean_st_ref_get(x_10, x_125);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_131 = lean_ctor_get(x_129, 1);
x_132 = lean_ctor_get(x_129, 0);
lean_dec(x_132);
x_133 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__19;
lean_inc(x_128);
lean_ctor_set_tag(x_129, 2);
lean_ctor_set(x_129, 1, x_133);
lean_ctor_set(x_129, 0, x_128);
x_134 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_135 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_128);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_128);
lean_ctor_set(x_136, 1, x_134);
lean_ctor_set(x_136, 2, x_135);
x_137 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__21;
lean_inc(x_128);
x_138 = l_Lean_Syntax_node1(x_128, x_137, x_136);
x_139 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5;
lean_inc(x_128);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Array_append___rarg(x_135, x_16);
lean_dec(x_16);
lean_inc(x_128);
x_142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_142, 0, x_128);
lean_ctor_set(x_142, 1, x_134);
lean_ctor_set(x_142, 2, x_141);
x_143 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6;
lean_inc(x_128);
x_144 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_144, 0, x_128);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__23;
lean_inc(x_128);
x_146 = l_Lean_Syntax_node3(x_128, x_145, x_140, x_142, x_144);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__24;
lean_inc(x_128);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_128);
lean_ctor_set(x_148, 1, x_134);
lean_ctor_set(x_148, 2, x_147);
x_149 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18;
x_150 = l_Lean_Syntax_node4(x_128, x_149, x_129, x_138, x_146, x_148);
x_17 = x_150;
x_18 = x_131;
goto block_123;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_124, 0);
lean_inc(x_151);
lean_dec(x_124);
x_152 = lean_array_push(x_135, x_151);
x_153 = l_Array_append___rarg(x_135, x_152);
lean_dec(x_152);
lean_inc(x_128);
x_154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_154, 0, x_128);
lean_ctor_set(x_154, 1, x_134);
lean_ctor_set(x_154, 2, x_153);
x_155 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18;
x_156 = l_Lean_Syntax_node4(x_128, x_155, x_129, x_138, x_146, x_154);
x_17 = x_156;
x_18 = x_131;
goto block_123;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_157 = lean_ctor_get(x_129, 1);
lean_inc(x_157);
lean_dec(x_129);
x_158 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__19;
lean_inc(x_128);
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_128);
lean_ctor_set(x_159, 1, x_158);
x_160 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10;
x_161 = l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10;
lean_inc(x_128);
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_128);
lean_ctor_set(x_162, 1, x_160);
lean_ctor_set(x_162, 2, x_161);
x_163 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__21;
lean_inc(x_128);
x_164 = l_Lean_Syntax_node1(x_128, x_163, x_162);
x_165 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5;
lean_inc(x_128);
x_166 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_166, 0, x_128);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Array_append___rarg(x_161, x_16);
lean_dec(x_16);
lean_inc(x_128);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_128);
lean_ctor_set(x_168, 1, x_160);
lean_ctor_set(x_168, 2, x_167);
x_169 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6;
lean_inc(x_128);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_128);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__23;
lean_inc(x_128);
x_172 = l_Lean_Syntax_node3(x_128, x_171, x_166, x_168, x_170);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__24;
lean_inc(x_128);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_128);
lean_ctor_set(x_174, 1, x_160);
lean_ctor_set(x_174, 2, x_173);
x_175 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18;
x_176 = l_Lean_Syntax_node4(x_128, x_175, x_159, x_164, x_172, x_174);
x_17 = x_176;
x_18 = x_157;
goto block_123;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_124, 0);
lean_inc(x_177);
lean_dec(x_124);
x_178 = lean_array_push(x_161, x_177);
x_179 = l_Array_append___rarg(x_161, x_178);
lean_dec(x_178);
lean_inc(x_128);
x_180 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_180, 0, x_128);
lean_ctor_set(x_180, 1, x_160);
lean_ctor_set(x_180, 2, x_179);
x_181 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18;
x_182 = l_Lean_Syntax_node4(x_128, x_181, x_159, x_164, x_172, x_180);
x_17 = x_182;
x_18 = x_157;
goto block_123;
}
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_219 = !lean_is_exclusive(x_12);
if (x_219 == 0)
{
return x_12;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_12, 0);
x_221 = lean_ctor_get(x_12, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_12);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_20);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_22);
lean_ctor_set(x_23, 5, x_19);
x_24 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3;
x_25 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_3, x_23, x_4, x_24, x_19, x_12, x_13, x_14, x_15, x_16);
return x_25;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("an applicable rewrite lemma", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_2);
x_16 = lean_array_mk(x_2);
x_17 = lean_array_size(x_16);
x_18 = lean_box_usize(x_17);
x_19 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed__const__1;
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___boxed), 11, 6);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_16);
lean_closure_set(x_20, 3, x_2);
lean_closure_set(x_20, 4, x_3);
lean_closure_set(x_20, 5, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_21 = l_Lean_Meta_withExposedNames___rarg(x_20, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3(x_29, x_28, x_1, x_5, x_26, x_27, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_34 = x_22;
} else {
 lean_dec_ref(x_22);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_36 = x_23;
} else {
 lean_dec_ref(x_23);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_39 = x_24;
} else {
 lean_dec_ref(x_24);
 x_39 = lean_box(0);
}
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
lean_dec(x_3);
lean_ctor_set(x_6, 0, x_72);
x_42 = x_6;
goto block_71;
}
else
{
lean_object* x_73; 
lean_free_object(x_6);
lean_dec(x_3);
x_73 = lean_box(0);
x_42 = x_73;
goto block_71;
}
block_71:
{
lean_object* x_43; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_35);
x_43 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_33, x_35, x_41, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(7, 2, 0);
} else {
 x_47 = x_39;
 lean_ctor_set_tag(x_47, 7);
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
x_48 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
if (lean_is_scalar(x_36)) {
 x_49 = lean_alloc_ctor(7, 2, 0);
} else {
 x_49 = x_36;
 lean_ctor_set_tag(x_49, 7);
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
if (lean_is_scalar(x_34)) {
 x_50 = lean_alloc_ctor(7, 2, 0);
} else {
 x_50 = x_34;
 lean_ctor_set_tag(x_50, 7);
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_37);
x_51 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__3;
x_52 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_51, x_50);
x_53 = 0;
x_54 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_52, x_53, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_45);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_61 = lean_ctor_get(x_44, 0);
lean_inc(x_61);
lean_dec(x_44);
x_62 = lean_ctor_get(x_43, 1);
lean_inc(x_62);
lean_dec(x_43);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3(x_38, x_37, x_1, x_5, x_63, x_64, x_65, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_62);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
return x_43;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_43, 0);
x_69 = lean_ctor_get(x_43, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_43);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_6, 0);
lean_inc(x_74);
lean_dec(x_6);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_3, 0);
lean_inc(x_103);
lean_dec(x_3);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_75 = x_104;
goto block_102;
}
else
{
lean_object* x_105; 
lean_dec(x_3);
x_105 = lean_box(0);
x_75 = x_105;
goto block_102;
}
block_102:
{
lean_object* x_76; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_35);
x_76 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic(x_33, x_35, x_74, x_75, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_1);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17;
if (lean_is_scalar(x_39)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_39;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_35);
x_81 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18;
if (lean_is_scalar(x_36)) {
 x_82 = lean_alloc_ctor(7, 2, 0);
} else {
 x_82 = x_36;
 lean_ctor_set_tag(x_82, 7);
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
if (lean_is_scalar(x_34)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_34;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_37);
x_84 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__3;
x_85 = l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg(x_84, x_83);
x_86 = 0;
x_87 = l_Lean_log___at_Lean_Elab_Tactic_closeUsingOrAdmit___spec__3(x_85, x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_78);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_92 = lean_ctor_get(x_77, 0);
lean_inc(x_92);
lean_dec(x_77);
x_93 = lean_ctor_get(x_76, 1);
lean_inc(x_93);
lean_dec(x_76);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_box(0);
x_97 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3(x_38, x_37, x_1, x_5, x_94, x_95, x_96, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_98 = lean_ctor_get(x_76, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_76, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_100 = x_76;
} else {
 lean_dec_ref(x_76);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_14);
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
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_21);
if (x_106 == 0)
{
return x_21;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_21, 0);
x_108 = lean_ctor_get(x_21, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_21);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
}
lean_object* initialize_Lean_Server_CodeActions(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_TryThis(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Hint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_CodeActions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Hint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__1);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__2();
l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3___boxed__const__1 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3___boxed__const__1);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___closed__3);
l_Lean_Meta_Tactic_TryThis_tryThisWidget = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__1);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__2);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__3);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__4);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__5);
l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__6 = _init_l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1___closed__6);
if (builtin) {res = l_Lean_Meta_Tactic_TryThis_tryThisWidget___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisWidget__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1 = _init_l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__1);
l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2 = _init_l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__2);
l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3 = _init_l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1___closed__3);
if (builtin) {res = l_Lean_Meta_Hint_tryThisDiffWidget___regBuiltin_Lean_Meta_Hint_tryThisDiffWidget__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__1);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__2);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__3);
l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4 = _init_l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_Lean_Meta_Tactic_TryThis_tryThisProvider___spec__1___closed__4);
l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisProvider___closed__1);
l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__1);
l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__2);
l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1___closed__3);
if (builtin) {res = l_Lean_Meta_Tactic_TryThis_tryThisProvider___regBuiltin_Lean_Meta_Tactic_TryThis_tryThisProvider__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___lambda__1___closed__1);
l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__1);
l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__2);
l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__3);
l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__4);
l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSyntax___closed__5);
l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__1);
l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_delabToRefinableSuggestion___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__3 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__3);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__4 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__4);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__5 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addSuggestionCore___closed__5);
l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__1);
l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addSuggestion___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Meta_Tactic_TryThis_addSuggestions___spec__2___closed__2);
l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__1);
l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addSuggestions___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_evalTacticWithState___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__3);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__4);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__5);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__6);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__7);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__8);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__9);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__10);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__11);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__12);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__13);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__14);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__15);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__16);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__17);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkValidatedTactic___closed__18);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__3);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__4);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__5);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__6 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkFailedToMakeTacticMsg___closed__6);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__3 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__3);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__4 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__1___closed__4);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__4 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___lambda__2___closed__4);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_mkExactSuggestionSyntax___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___spec__1___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__1___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__3 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__3);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__4 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__4);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__5 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__5);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__6);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__7 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__7);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__8 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__8);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__9 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__9);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__10);
l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11 = _init_l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_TryThis_0__Lean_Meta_Tactic_TryThis_addExactSuggestionCore___lambda__2___closed__11);
l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__1 = _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__1);
l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2 = _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__2);
l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__3 = _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__3();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__3);
l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__4 = _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__4();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___lambda__2___closed__4);
l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1 = _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__1);
l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__2 = _init_l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__2();
lean_mark_persistent(l_Lean_logAt___at_Lean_Meta_Tactic_TryThis_addExactSuggestions___spec__4___closed__2);
l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__1);
l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addExactSuggestions___closed__2);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__1);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__2);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__3);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__4);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__5);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__6 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__6);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__7);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__8 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__8);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__9);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__10);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__11);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__12 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__12);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__13);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__14 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__14);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__15);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__16 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__16();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__16);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__17 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__17();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__17);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__18 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__18();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__18);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__19);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__20);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__21 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__21();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__21);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__22);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__23 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__23();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__23);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__24);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__25 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__25();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__25);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__26);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__27 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__27();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__27);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__28);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__29);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__30 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__30();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__30);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__31 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__31();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__31);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__32 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__32();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__32);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__33);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__34 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__34();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__34);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__35 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__35();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__35);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__36);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__37 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__37();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__37);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__38);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__39 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__39();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__39);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__40);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__41 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__41();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__41);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__42 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__42();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__42);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__43 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__43();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__43);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__44 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__44();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__44);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__45 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__45();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__45);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__46 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__46();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__46);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__47 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__47();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__47);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__48 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__48();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__48);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__49 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__49();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__49);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__50 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__50();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__50);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__51 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__51();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__51);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__52 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__52();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__52);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__53 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__53();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__53);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__54 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__54();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__54);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__55 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__55();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__55);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__56 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__56();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__56);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__57 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__57();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__57);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__58 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__58();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__58);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__59 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__59();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__59);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__60 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__60();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__60);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__61 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__61();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__61);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__62 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__62();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__62);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__63 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__63();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__63);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__64 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__64();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__64);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__65 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__65();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__65);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__66 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__66();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__66);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__67 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__67();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__67);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__68 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__68();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__68);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__69 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__69();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__69);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__70 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__70();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__70);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__71 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__71();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__71);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__72 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__72();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__72);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__73 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__73();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__73);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__74 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__74();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__74);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__75 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__75();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__75);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__76 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__76();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__76);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__77 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__77();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__77);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__78);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__79 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__79();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__79);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__80 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__80();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__80);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__81 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__81();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__81);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__82);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__83 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__83();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__83);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__84);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__85);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__86 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__86();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__86);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__87);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__88 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__88();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__88);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__89 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__89();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___lambda__2___closed__89);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__1);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__2);
l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addHaveSuggestion___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__7);
l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__8 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__1___closed__8);
l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__1 = _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__1);
l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2 = _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__2);
l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__3 = _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__3);
l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4 = _init_l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___spec__2___closed__4);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__1);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__2);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__3);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__4 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__4);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__5);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__6);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__7 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__7);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__8 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__8);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__9 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__9);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__10);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__11 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__11);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__12 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__12);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__13 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__13);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__14 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__14);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__15 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__15);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__16 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__16();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__16);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__17 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__17();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__17);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__18);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__19 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__19();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__19);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__20 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__20();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__20);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__21 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__21();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__21);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__22 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__22();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__22);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__23 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__23();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__23);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__24 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__24();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__24);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__25 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__25();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__25);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__26 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__26();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__26);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__27 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__27();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__27);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__28 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__28();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__28);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__29 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__29();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___lambda__2___closed__29);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__1);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__2);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__3 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__3();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___closed__3);
l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed__const__1 = _init_l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
