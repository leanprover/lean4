// Lean compiler output
// Module: Lean.Elab.BuiltinCommand
// Imports: Init Lean.Elab.DeclarationRange Lean.DocString Lean.Util.CollectLevelParams Lean.Elab.Eval Lean.Elab.Command Lean.Elab.Open
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
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSetOption___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__8;
static lean_object* l_Lean_Elab_Command_elabCheckCore___closed__3;
lean_object* l_Lean_KVMap_setBool(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSection(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSection___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCheckFailure___closed__2;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__4;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__3;
lean_object* l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2(lean_object*);
static lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Command_elabModuleDoc___closed__4;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__7;
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__5;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_elabNonComputableSection___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCheckCore___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__25;
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withNamespace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabAddDeclDoc___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTRAux___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Command_elabOpen___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabCheckCore___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSection___closed__2;
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
static lean_object* l_Lean_Elab_Command_elabReduce___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__1;
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_Elab_Command_elabModuleDoc___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__4;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
lean_object* l_Lean_toMessageList(lean_object*);
static lean_object* l_Lean_Elab_Command_elabCheckCore___closed__1;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabExport___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___at_Lean_Elab_Command_elabExport___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__2;
lean_object* l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSection___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabModuleDoc___closed__3;
lean_object* l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_append___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Command_elabEnd___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkAnonymousScope(lean_object*);
static lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1;
static lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__2;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabNonComputableSection___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__6;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__8;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__3;
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__3;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2;
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheck(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Command_elabOpen___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabModuleDoc___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAddDeclDoc___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNonComputableSection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
lean_object* l_Std_mkHashSetImp___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__5;
static lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_elabChoiceAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkAnonymousScope___boxed(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabModuleDoc___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabOpen(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__6;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Command_elabOpen___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_elabSynth___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___at_Lean_Elab_Command_elabUniverse___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__7;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__27;
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabCheckCore___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__6;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__1;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__3;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__8;
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg(lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Command_elabExport___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_elabCheckFailure___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabOpen___lambda__1(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11;
lean_object* l_Lean_Elab_Term_evalTerm___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__2;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__4;
lean_object* l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__23;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__4;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Command_elabEnd___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Command_elabExport___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabAddDeclDoc___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__7;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__3;
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__2;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__31;
static lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__1;
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__2;
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Command_elabOpen___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__2;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__2;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__2;
lean_object* l_Lean_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEnd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabSection___closed__4;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__4;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__2;
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Command_elabEnd___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___at_Lean_Elab_Command_elabVariable___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__15;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabExport___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__12;
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabOpen___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__2;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3;
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__6;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabAddDeclDoc___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__6;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_popScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabReduce___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__4;
lean_object* l_Lean_Elab_Command_getBracketedBinderIds(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26;
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__1;
uint8_t l_Array_contains___at_Lean_findField_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
lean_object* l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Command_elabOpen___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__9;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Command_elabOpen___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Command_elabEnd___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__3;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__1;
lean_object* l_Lean_Name_getNumParts(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAddDeclDoc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
lean_object* lean_expr_dbg_to_string(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__6;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Command_elabOpen___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
static lean_object* l_Lean_Elab_Command_elabSynth___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__10;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbortTerm___at_Lean_Elab_Term_evalTerm___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_elabEnd___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__6;
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabSetOption___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
LEAN_EXPORT lean_object* l_Lean_activateScoped___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__4;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabVariable___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEnd(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__5;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__2;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabModuleDoc___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabExport___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenScoped___at_Lean_Elab_Command_elabOpen___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabExport___spec__18(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__5;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabOpen___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitQuot___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___at_Lean_Elab_Command_elabVariable___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__2;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__2;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabReduce___lambda__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadQuotation_addMacroScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__5;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__19;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAddDeclDoc___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__12;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addUnivLevel(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__2;
lean_object* l_List_drop___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNonComputableSection(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__1;
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabExport___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_failIfSucceeds___closed__1;
static lean_object* l_Lean_Elab_Command_elabAddDeclDoc___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkEndHeader(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection___closed__2;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__4;
extern lean_object* l___private_Lean_DocString_0__Lean_moduleDocExt;
static lean_object* l_Lean_Elab_Command_elabExport___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__18;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__5;
static lean_object* l_Lean_Elab_Command_elabReduce___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Command_elabAddDeclDoc___closed__1;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__28;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__15;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__13;
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__12;
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__30;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabExport___closed__1;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce(lean_object*);
lean_object* l_panic___at___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___spec__9(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_activateScoped___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__3;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3;
static lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__2;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__4;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__4;
lean_object* l_Lean_Elab_Command_modifyScope(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__6;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__1;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__6;
static lean_object* l_Lean_Elab_Command_elabEnd___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabExport___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__5;
static lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabModuleDoc___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__3;
static lean_object* l_Lean_Elab_Command_elabAddDeclDoc___closed__4;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabVariable___closed__2;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__7;
extern lean_object* l_Lean_Elab_Command_instInhabitedScope;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__1;
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__20;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__6;
lean_object* l_Lean_Syntax_getOptionalIdent_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck___closed__3;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__1___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__4;
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__3;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabNamespace___closed__2;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabExport___spec__17(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__7;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabModuleDoc___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInCmd___closed__1;
static lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_popScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
static lean_object* l_Lean_Elab_Command_elabCheckFailure___closed__3;
static lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__6;
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__5;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__5;
lean_object* l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__6;
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_elabChoiceAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__24;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_getScopes___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabModuleDoc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__3;
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__2;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__16;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object*);
lean_object* l_Lean_Elab_Term_exprToSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__4;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkEndHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__10;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__2;
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__5;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__5;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__5;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__2;
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__22;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3;
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_resetMessageLog(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSetOption___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__3;
extern lean_object* l_Lean_scopedEnvExtensionsRef;
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__21;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2;
lean_object* l_Lean_Elab_Command_getScope___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenScoped___at_Lean_Elab_Command_elabOpen___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__1;
lean_object* l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadQuotation_addMacroScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabCheckCore___closed__4;
static lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange(lean_object*);
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(lean_object*);
static lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Command_elabExport___spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Command_elabOpen___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__5;
uint8_t l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages___boxed(lean_object*);
lean_object* l_Lean_Elab_logException___at_Lean_Elab_Command_elabCommand___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___at_Lean_Elab_Command_elabUniverse___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__1;
lean_object* l_Lean_Elab_Term_withAutoBoundImplicit___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__3;
static lean_object* l_Lean_Elab_Command_elabSynth___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__5;
lean_object* l_Lean_mkSimpleThunk(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandInCmd___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange(lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__3;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSection___closed__3;
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__29;
static lean_object* l_Lean_Elab_Command_elabNamespace___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__2;
static lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabAddDeclDoc___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSetOption___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__7;
static lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Command_elabOpen___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__7;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabExport___closed__3;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabModuleDoc___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__14;
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Command_elabEnd___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabModuleDoc___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_2, x_20, x_4, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabModuleDoc___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
x_7 = l_Lean_Syntax_getPos_x3f(x_1, x_6);
x_8 = l_Lean_Syntax_getTailPos_x3f(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_FileMap_toPosition(x_5, x_9);
lean_inc(x_10);
x_11 = l_Lean_FileMap_leanPosToLspPos(x_5, x_10);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_FileMap_toPosition(x_5, x_16);
lean_dec(x_16);
lean_inc(x_17);
x_18 = l_Lean_FileMap_leanPosToLspPos(x_5, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_dec(x_7);
x_23 = l_Lean_FileMap_toPosition(x_5, x_22);
lean_dec(x_22);
lean_inc(x_23);
x_24 = l_Lean_FileMap_leanPosToLspPos(x_5, x_23);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_25);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lean_FileMap_toPosition(x_5, x_29);
lean_dec(x_29);
lean_inc(x_30);
x_31 = l_Lean_FileMap_leanPosToLspPos(x_5, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabModuleDoc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected module doc string", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabModuleDoc___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabModuleDoc___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabModuleDoc___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabModuleDoc___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabModuleDoc___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_DocString_0__Lean_moduleDocExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabModuleDoc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_extract(x_7, x_11, x_10);
lean_dec(x_10);
lean_dec(x_7);
x_13 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabModuleDoc___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_14);
x_22 = l_Lean_Elab_Command_elabModuleDoc___closed__5;
x_23 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_22, x_20, x_21);
lean_ctor_set(x_17, 0, x_23);
x_24 = lean_st_ref_set(x_3, x_17, x_18);
lean_dec(x_3);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
x_33 = lean_ctor_get(x_17, 2);
x_34 = lean_ctor_get(x_17, 3);
x_35 = lean_ctor_get(x_17, 4);
x_36 = lean_ctor_get(x_17, 5);
x_37 = lean_ctor_get(x_17, 6);
x_38 = lean_ctor_get(x_17, 7);
x_39 = lean_ctor_get(x_17, 8);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_12);
lean_ctor_set(x_40, 1, x_14);
x_41 = l_Lean_Elab_Command_elabModuleDoc___closed__5;
x_42 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_41, x_31, x_40);
x_43 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 3, x_34);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_36);
lean_ctor_set(x_43, 6, x_37);
lean_ctor_set(x_43, 7, x_38);
lean_ctor_set(x_43, 8, x_39);
x_44 = lean_st_ref_set(x_3, x_43, x_18);
lean_dec(x_3);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_6);
x_50 = l_Lean_indentD(x_49);
x_51 = l_Lean_Elab_Command_elabModuleDoc___closed__2;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabModuleDoc___spec__1(x_1, x_54, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabModuleDoc___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabModuleDoc___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabModuleDoc___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getDeclarationRange___at_Lean_Elab_Command_elabModuleDoc___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Command", 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4;
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("moduleDoc", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabModuleDoc", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabModuleDoc), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__8;
x_4 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__13;
x_5 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__15;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(21u);
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__1;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__2;
x_4 = lean_unsigned_to_nat(73u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__4;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__5;
x_4 = lean_unsigned_to_nat(49u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__13;
x_3 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_st_ref_take(x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_6, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_box(0);
x_3 = x_20;
x_4 = x_21;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
x_28 = lean_ctor_get(x_12, 5);
x_29 = lean_ctor_get(x_12, 6);
x_30 = lean_ctor_get(x_12, 7);
x_31 = lean_ctor_get(x_12, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_32 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_10, x_23);
lean_dec(x_10);
x_33 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_28);
lean_ctor_set(x_33, 6, x_29);
lean_ctor_set(x_33, 7, x_30);
lean_ctor_set(x_33, 8, x_31);
x_34 = lean_st_ref_set(x_6, x_33, x_13);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_38 = lean_box(0);
x_3 = x_37;
x_4 = x_38;
x_7 = x_35;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_scopedEnvExtensionsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__2(x_6, x_9, x_10, x_11, x_1, x_2, x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_5);
x_11 = lean_array_uget(x_2, x_4);
x_12 = lean_st_ref_take(x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_1);
x_17 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_11, x_16, x_1);
lean_ctor_set(x_13, 0, x_17);
x_18 = lean_st_ref_set(x_7, x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = lean_box(0);
x_4 = x_21;
x_5 = x_22;
x_8 = x_19;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
x_26 = lean_ctor_get(x_13, 2);
x_27 = lean_ctor_get(x_13, 3);
x_28 = lean_ctor_get(x_13, 4);
x_29 = lean_ctor_get(x_13, 5);
x_30 = lean_ctor_get(x_13, 6);
x_31 = lean_ctor_get(x_13, 7);
x_32 = lean_ctor_get(x_13, 8);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
lean_inc(x_1);
x_33 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_11, x_24, x_1);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_34, 6, x_30);
lean_ctor_set(x_34, 7, x_31);
lean_ctor_set(x_34, 8, x_32);
x_35 = lean_st_ref_set(x_7, x_34, x_14);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = 1;
x_38 = lean_usize_add(x_4, x_37);
x_39 = lean_box(0);
x_4 = x_38;
x_5 = x_39;
x_8 = x_36;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_get_size(x_7);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__4(x_1, x_7, x_10, x_11, x_12, x_2, x_3, x_8);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_st_ref_take(x_6, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_4);
x_25 = l_Lean_Environment_registerNamespace(x_23, x_4);
x_26 = l_Lean_Elab_Command_instInhabitedScope;
x_27 = l_List_head_x21___rarg(x_26, x_24);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*7);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
lean_inc(x_4);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set_uint8(x_27, sizeof(void*)*7, x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_20, 2, x_32);
lean_ctor_set(x_20, 0, x_25);
x_33 = lean_st_ref_set(x_6, x_20, x_21);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_8 = x_34;
goto block_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_27, 1);
x_36 = lean_ctor_get(x_27, 3);
x_37 = lean_ctor_get(x_27, 4);
x_38 = lean_ctor_get(x_27, 5);
x_39 = lean_ctor_get(x_27, 6);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
lean_inc(x_4);
x_40 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_4);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_37);
lean_ctor_set(x_40, 5, x_38);
lean_ctor_set(x_40, 6, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*7, x_2);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_20, 2, x_41);
lean_ctor_set(x_20, 0, x_25);
x_42 = lean_st_ref_set(x_6, x_20, x_21);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_8 = x_43;
goto block_18;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_27, 2);
lean_dec(x_45);
x_46 = lean_ctor_get(x_27, 0);
lean_dec(x_46);
x_47 = 1;
lean_inc(x_4);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set_uint8(x_27, sizeof(void*)*7, x_47);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_27);
lean_ctor_set(x_48, 1, x_24);
lean_ctor_set(x_20, 2, x_48);
lean_ctor_set(x_20, 0, x_25);
x_49 = lean_st_ref_set(x_6, x_20, x_21);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_8 = x_50;
goto block_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_51 = lean_ctor_get(x_27, 1);
x_52 = lean_ctor_get(x_27, 3);
x_53 = lean_ctor_get(x_27, 4);
x_54 = lean_ctor_get(x_27, 5);
x_55 = lean_ctor_get(x_27, 6);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_27);
x_56 = 1;
lean_inc(x_4);
x_57 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_51);
lean_ctor_set(x_57, 2, x_4);
lean_ctor_set(x_57, 3, x_52);
lean_ctor_set(x_57, 4, x_53);
lean_ctor_set(x_57, 5, x_54);
lean_ctor_set(x_57, 6, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*7, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_24);
lean_ctor_set(x_20, 2, x_58);
lean_ctor_set(x_20, 0, x_25);
x_59 = lean_st_ref_set(x_6, x_20, x_21);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_8 = x_60;
goto block_18;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_61 = lean_ctor_get(x_20, 0);
x_62 = lean_ctor_get(x_20, 1);
x_63 = lean_ctor_get(x_20, 2);
x_64 = lean_ctor_get(x_20, 3);
x_65 = lean_ctor_get(x_20, 4);
x_66 = lean_ctor_get(x_20, 5);
x_67 = lean_ctor_get(x_20, 6);
x_68 = lean_ctor_get(x_20, 7);
x_69 = lean_ctor_get(x_20, 8);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_20);
lean_inc(x_4);
x_70 = l_Lean_Environment_registerNamespace(x_61, x_4);
x_71 = l_Lean_Elab_Command_instInhabitedScope;
x_72 = l_List_head_x21___rarg(x_71, x_63);
x_73 = lean_ctor_get_uint8(x_72, sizeof(void*)*7);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 4);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 6);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 lean_ctor_release(x_72, 6);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
lean_inc(x_4);
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(0, 7, 1);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_3);
lean_ctor_set(x_80, 1, x_74);
lean_ctor_set(x_80, 2, x_4);
lean_ctor_set(x_80, 3, x_75);
lean_ctor_set(x_80, 4, x_76);
lean_ctor_set(x_80, 5, x_77);
lean_ctor_set(x_80, 6, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*7, x_2);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_63);
x_82 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_62);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_64);
lean_ctor_set(x_82, 4, x_65);
lean_ctor_set(x_82, 5, x_66);
lean_ctor_set(x_82, 6, x_67);
lean_ctor_set(x_82, 7, x_68);
lean_ctor_set(x_82, 8, x_69);
x_83 = lean_st_ref_set(x_6, x_82, x_21);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_8 = x_84;
goto block_18;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_72, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_72, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 5);
lean_inc(x_88);
x_89 = lean_ctor_get(x_72, 6);
lean_inc(x_89);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 lean_ctor_release(x_72, 3);
 lean_ctor_release(x_72, 4);
 lean_ctor_release(x_72, 5);
 lean_ctor_release(x_72, 6);
 x_90 = x_72;
} else {
 lean_dec_ref(x_72);
 x_90 = lean_box(0);
}
x_91 = 1;
lean_inc(x_4);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 7, 1);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_92, 2, x_4);
lean_ctor_set(x_92, 3, x_86);
lean_ctor_set(x_92, 4, x_87);
lean_ctor_set(x_92, 5, x_88);
lean_ctor_set(x_92, 6, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*7, x_91);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_63);
x_94 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_94, 0, x_70);
lean_ctor_set(x_94, 1, x_62);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_94, 3, x_64);
lean_ctor_set(x_94, 4, x_65);
lean_ctor_set(x_94, 5, x_66);
lean_ctor_set(x_94, 6, x_67);
lean_ctor_set(x_94, 7, x_68);
lean_ctor_set(x_94, 8, x_69);
x_95 = lean_st_ref_set(x_6, x_94, x_21);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_8 = x_96;
goto block_18;
}
}
block_18:
{
lean_object* x_9; 
x_9 = l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1(x_5, x_6, x_8);
if (x_1 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = l_Lean_activateScoped___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__3(x_4, x_5, x_6, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__4(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_activateScoped___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid scope", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_4);
x_11 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(x_1, x_2, x_9, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_5, x_12);
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope(x_1, x_2, x_10, x_16, x_4, x_5, x_15);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
x_21 = l_Lean_Name_str___override(x_20, x_10);
x_22 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope(x_1, x_2, x_10, x_21, x_4, x_5, x_19);
lean_dec(x_4);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
default: 
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_27 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__2;
x_28 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_27, x_4, x_5, x_6);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = 1;
x_6 = 0;
x_7 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = 0;
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(x_6, x_7, x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_4);
x_10 = lean_apply_3(x_2, x_3, x_4, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_14, 2);
x_18 = l_Lean_Name_getNumParts(x_1);
lean_dec(x_1);
x_19 = l_List_drop___rarg(x_18, x_17);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_19);
x_20 = lean_st_ref_set(x_4, x_14, x_15);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_14, 5);
x_31 = lean_ctor_get(x_14, 6);
x_32 = lean_ctor_get(x_14, 7);
x_33 = lean_ctor_get(x_14, 8);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_34 = l_Lean_Name_getNumParts(x_1);
lean_dec(x_1);
x_35 = l_List_drop___rarg(x_34, x_27);
lean_dec(x_27);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_28);
lean_ctor_set(x_36, 4, x_29);
lean_ctor_set(x_36, 5, x_30);
lean_ctor_set(x_36, 6, x_31);
lean_ctor_set(x_36, 7, x_32);
lean_ctor_set(x_36, 8, x_33);
x_37 = lean_st_ref_set(x_4, x_36, x_15);
lean_dec(x_4);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
return x_8;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_withNamespace___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_st_ref_take(x_6, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_ScopedEnvExtension_popScope___rarg(x_10, x_15);
lean_dec(x_10);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_st_ref_set(x_6, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_box(0);
x_3 = x_20;
x_4 = x_21;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
x_28 = lean_ctor_get(x_12, 5);
x_29 = lean_ctor_get(x_12, 6);
x_30 = lean_ctor_get(x_12, 7);
x_31 = lean_ctor_get(x_12, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_32 = l_Lean_ScopedEnvExtension_popScope___rarg(x_10, x_23);
lean_dec(x_10);
x_33 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_28);
lean_ctor_set(x_33, 6, x_29);
lean_ctor_set(x_33, 7, x_30);
lean_ctor_set(x_33, 8, x_31);
x_34 = lean_st_ref_set(x_6, x_33, x_13);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = 1;
x_37 = lean_usize_add(x_3, x_36);
x_38 = lean_box(0);
x_3 = x_37;
x_4 = x_38;
x_7 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_get_size(x_6);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__2(x_6, x_9, x_10, x_11, x_1, x_2, x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_popScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__1(x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_17 = lean_box(0);
x_1 = x_13;
x_2 = x_16;
x_5 = x_17;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = l_Std_Range_forIn_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__3(x_1, x_5, x_1, x_6, x_7, x_2, x_3, x_4);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_popScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_popScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Range_forIn_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkAnonymousScope(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_6 = lean_string_dec_eq(x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkAnonymousScope___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkAnonymousScope(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkEndHeader(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 1:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_string_dec_eq(x_9, x_7);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
}
}
}
default: 
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkEndHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkEndHeader(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namespace", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabNamespace___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabNamespace___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getId(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = 0;
x_13 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(x_11, x_12, x_10, x_2, x_3, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabNamespace", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNamespace___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabNamespace___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(62u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(65u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__1;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__2;
x_4 = lean_unsigned_to_nat(45u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(62u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(62u);
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__4;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__5;
x_4 = lean_unsigned_to_nat(51u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("section", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabSection___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSection___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSection___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSection___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabSection___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Lean_Syntax_matchesNull(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_matchesNull(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_20 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope(x_18, x_18, x_19, x_17, x_2, x_3, x_16);
lean_dec(x_2);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_9, x_21);
lean_dec(x_9);
x_23 = l_Lean_Elab_Command_elabSection___closed__4;
lean_inc(x_22);
x_24 = l_Lean_Syntax_isOfKind(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_2);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Lean_Syntax_getId(x_22);
lean_dec(x_22);
x_27 = 0;
x_28 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(x_27, x_27, x_26, x_2, x_3, x_4);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSection(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSection", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSection___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSection___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabSection___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSection___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSection___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(67u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(71u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__1;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__2;
x_4 = lean_unsigned_to_nat(54u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(67u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(67u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__4;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__5;
x_4 = lean_unsigned_to_nat(47u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSection_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSection___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabNonComputableSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("noncomputableSection", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabNonComputableSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabNonComputableSection___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNonComputableSection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabNonComputableSection___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_11 = l_Lean_Syntax_matchesNull(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_matchesNull(x_9, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = 1;
x_21 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_22 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope(x_19, x_20, x_21, x_18, x_2, x_3, x_17);
lean_dec(x_2);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_9, x_23);
lean_dec(x_9);
x_25 = l_Lean_Elab_Command_elabSection___closed__4;
lean_inc(x_24);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_2);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_28 = l_Lean_Syntax_getId(x_24);
lean_dec(x_24);
x_29 = 0;
x_30 = 1;
x_31 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes(x_29, x_30, x_28, x_2, x_3, x_4);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabNonComputableSection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabNonComputableSection(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabNonComputableSection", 24);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabNonComputableSection___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabNonComputableSection___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(73u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(77u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__1;
x_2 = lean_unsigned_to_nat(43u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__2;
x_4 = lean_unsigned_to_nat(54u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(73u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(73u);
x_2 = lean_unsigned_to_nat(71u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__4;
x_2 = lean_unsigned_to_nat(47u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__5;
x_4 = lean_unsigned_to_nat(71u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Command_elabEnd___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Command_elabEnd___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 7);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_18, 1);
x_24 = l_Std_PersistentArray_push___rarg(x_23, x_1);
lean_ctor_set(x_18, 1, x_24);
x_25 = lean_st_ref_set(x_3, x_17, x_19);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = l_Std_PersistentArray_push___rarg(x_34, x_1);
x_36 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_32);
lean_ctor_set(x_17, 7, x_36);
x_37 = lean_st_ref_set(x_3, x_17, x_19);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
x_44 = lean_ctor_get(x_17, 2);
x_45 = lean_ctor_get(x_17, 3);
x_46 = lean_ctor_get(x_17, 4);
x_47 = lean_ctor_get(x_17, 5);
x_48 = lean_ctor_get(x_17, 6);
x_49 = lean_ctor_get(x_17, 8);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_50 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
x_51 = lean_ctor_get(x_18, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_53 = x_18;
} else {
 lean_dec_ref(x_18);
 x_53 = lean_box(0);
}
x_54 = l_Std_PersistentArray_push___rarg(x_52, x_1);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 1);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_50);
x_56 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_44);
lean_ctor_set(x_56, 3, x_45);
lean_ctor_set(x_56, 4, x_46);
lean_ctor_set(x_56, 5, x_47);
lean_ctor_set(x_56, 6, x_48);
lean_ctor_set(x_56, 7, x_55);
lean_ctor_set(x_56, 8, x_49);
x_57 = lean_st_ref_set(x_3, x_56, x_19);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__2;
x_3 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Command_elabEnd___spec__4(x_17, x_2, x_3, x_15);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Command_elabEnd___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'end', name is missing", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'end', name mismatch", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEnd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkAnonymousScope(x_2);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__2;
x_10 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_9, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_checkEndHeader(x_13, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_box(0);
x_16 = l_List_mapTRAux___at_Lean_Elab_Command_elabEnd___spec__1(x_2, x_15);
x_17 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Command_elabEnd___spec__2(x_17, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Command_elabEnd___lambda__1___closed__4;
x_21 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_20, x_5, x_6, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'end', insufficient scopes", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEnd___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_87; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getOptionalIdent_x3f(x_6);
lean_dec(x_6);
x_87 = l_Lean_Elab_Command_getScopes___rarg(x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_8 = x_5;
x_9 = x_88;
x_10 = x_89;
goto block_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_7, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
lean_dec(x_87);
x_93 = l_Lean_Name_getNumParts(x_90);
lean_dec(x_90);
x_8 = x_93;
x_9 = x_91;
x_10 = x_92;
goto block_86;
}
block_86:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_lengthTRAux___rarg(x_9, x_11);
x_13 = lean_nat_dec_lt(x_8, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_14 = lean_st_ref_get(x_3, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_List_lengthTRAux___rarg(x_17, x_11);
lean_dec(x_17);
x_19 = lean_nat_sub(x_18, x_5);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_3, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_19);
x_25 = l_List_drop___rarg(x_19, x_24);
lean_dec(x_24);
lean_ctor_set(x_21, 2, x_25);
x_26 = lean_st_ref_set(x_3, x_21, x_22);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes(x_19, x_2, x_3, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_Command_elabEnd___closed__2;
x_31 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_30, x_2, x_3, x_29);
lean_dec(x_3);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
x_38 = lean_ctor_get(x_21, 2);
x_39 = lean_ctor_get(x_21, 3);
x_40 = lean_ctor_get(x_21, 4);
x_41 = lean_ctor_get(x_21, 5);
x_42 = lean_ctor_get(x_21, 6);
x_43 = lean_ctor_get(x_21, 7);
x_44 = lean_ctor_get(x_21, 8);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
lean_inc(x_19);
x_45 = l_List_drop___rarg(x_19, x_38);
lean_dec(x_38);
x_46 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_41);
lean_ctor_set(x_46, 6, x_42);
lean_ctor_set(x_46, 7, x_43);
lean_ctor_set(x_46, 8, x_44);
x_47 = lean_st_ref_set(x_3, x_46, x_22);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes(x_19, x_2, x_3, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Elab_Command_elabEnd___closed__2;
x_52 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_51, x_2, x_3, x_50);
lean_dec(x_3);
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_st_ref_take(x_3, x_10);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_58, 2);
lean_inc(x_8);
x_62 = l_List_drop___rarg(x_8, x_61);
lean_dec(x_61);
lean_ctor_set(x_58, 2, x_62);
x_63 = lean_st_ref_set(x_3, x_58, x_59);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes(x_8, x_2, x_3, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Command_elabEnd___lambda__1(x_7, x_9, x_1, x_66, x_2, x_3, x_67);
lean_dec(x_3);
lean_dec(x_66);
lean_dec(x_7);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
x_71 = lean_ctor_get(x_58, 2);
x_72 = lean_ctor_get(x_58, 3);
x_73 = lean_ctor_get(x_58, 4);
x_74 = lean_ctor_get(x_58, 5);
x_75 = lean_ctor_get(x_58, 6);
x_76 = lean_ctor_get(x_58, 7);
x_77 = lean_ctor_get(x_58, 8);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
lean_inc(x_8);
x_78 = l_List_drop___rarg(x_8, x_71);
lean_dec(x_71);
x_79 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_72);
lean_ctor_set(x_79, 4, x_73);
lean_ctor_set(x_79, 5, x_74);
lean_ctor_set(x_79, 6, x_75);
lean_ctor_set(x_79, 7, x_76);
lean_ctor_set(x_79, 8, x_77);
x_80 = lean_st_ref_set(x_3, x_79, x_59);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_popScopes(x_8, x_2, x_3, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Elab_Command_elabEnd___lambda__1(x_7, x_9, x_1, x_83, x_2, x_3, x_84);
lean_dec(x_3);
lean_dec(x_83);
lean_dec(x_7);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Command_elabEnd___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Command_elabEnd___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Command_elabEnd___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Command_elabEnd___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEnd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabEnd___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("end", 3);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabEnd", 7);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEnd), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(79u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__1;
x_2 = lean_unsigned_to_nat(28u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__2;
x_4 = lean_unsigned_to_nat(47u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(79u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(79u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__4;
x_2 = lean_unsigned_to_nat(32u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__5;
x_4 = lean_unsigned_to_nat(39u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEnd_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_elabChoiceAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Elab_Command_elabCommand(x_9, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1;
x_21 = lean_nat_dec_eq(x_20, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1;
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
lean_dec(x_2);
x_2 = x_31;
x_5 = x_25;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_elabChoiceAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_elabChoiceAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Syntax_getArgs(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_elabChoiceAux(x_5, x_6, x_2, x_3, x_4);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabChoice(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("choice", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Command_elabChoice___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabChoice", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabChoice___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabChoice___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabChoice___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabChoice___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabChoice___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(111u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(112u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__1;
x_2 = lean_unsigned_to_nat(29u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__2;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(111u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(111u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__4;
x_2 = lean_unsigned_to_nat(33u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__5;
x_4 = lean_unsigned_to_nat(43u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabChoice_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabChoice___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_3, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_apply_5(x_1, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_5 = x_12;
x_8 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___at_Lean_Elab_Command_elabUniverse___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_10 = l_Lean_Elab_Command_addUnivLevel(x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___at_Lean_Elab_Command_elabUniverse___spec__2(x_7, x_16, x_17, x_18, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_7);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___at_Lean_Elab_Command_elabUniverse___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabUniverse___spec__1___at_Lean_Elab_Command_elabUniverse___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("universe", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabUniverse", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabUniverse), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(114u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(115u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__1;
x_2 = lean_unsigned_to_nat(33u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__2;
x_4 = lean_unsigned_to_nat(28u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(114u);
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(114u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__4;
x_2 = lean_unsigned_to_nat(37u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__5;
x_4 = lean_unsigned_to_nat(49u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_1);
x_10 = lean_st_ref_set(x_3, x_6, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
x_20 = lean_ctor_get(x_6, 4);
x_21 = lean_ctor_get(x_6, 5);
x_22 = lean_ctor_get(x_6, 6);
x_23 = lean_ctor_get(x_6, 7);
x_24 = lean_ctor_get(x_6, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
x_26 = lean_st_ref_set(x_3, x_25, x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitQuot___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(4);
x_9 = lean_add_decl(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_2, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Command_instInhabitedScope;
x_16 = l_List_head_x21___rarg(x_15, x_14);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_KernelException_toMessageData(x_10, x_17);
x_19 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_18, x_1, x_2, x_13);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_20, x_1, x_2, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabInitQuot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_elabInitQuot(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("init_quot", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabInitQuot", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInitQuot___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(117u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(120u);
x_2 = lean_unsigned_to_nat(67u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__1;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__2;
x_4 = lean_unsigned_to_nat(67u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(117u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(117u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__4;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__5;
x_4 = lean_unsigned_to_nat(50u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown namespace '", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = l_Lean_ResolveName_resolveNamespace(x_8, x_12, x_17, x_1);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_13);
x_19 = 1;
x_20 = l_Lean_Name_toString(x_1, x_19);
x_21 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(x_26, x_2, x_3, x_16);
return x_27;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_ctor_get(x_28, 3);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_1);
x_31 = l_Lean_ResolveName_resolveNamespace(x_8, x_12, x_30, x_1);
lean_dec(x_12);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = 1;
x_33 = l_Lean_Name_toString(x_1, x_32);
x_34 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(x_39, x_2, x_3, x_29);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_29);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabExport___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_2, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_2, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_ResolveName_resolveGlobalName(x_9, x_13, x_17, x_1);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_ResolveName_resolveGlobalName(x_9, x_13, x_21, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_3, x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_1, x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__3;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__9(x_12, x_2, x_3, x_4, x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_6 = l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabExport___spec__7(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_List_filterTRAux___at_Lean_resolveGlobalConstCore___spec__1(x_7, x_9);
x_11 = l_List_isEmpty___rarg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6___lambda__1(x_10, x_9, x_12, x_2, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_14 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8(x_1, x_2, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Command_elabExport___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Expr_const___override(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_3, x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Command_elabExport___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Expr_const___override(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous identifier '", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: ", 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_1, x_9);
x_11 = lean_expr_dbg_to_string(x_10);
lean_dec(x_10);
x_12 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_List_mapTRAux___at_Lean_Elab_Command_elabExport___spec__10(x_9, x_7, x_9);
x_17 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(x_22, x_2, x_3, x_4, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_6, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
lean_dec(x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_24);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_const___override(x_1, x_32);
x_34 = lean_expr_dbg_to_string(x_33);
lean_dec(x_33);
x_35 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = l_List_mapTRAux___at_Lean_Elab_Command_elabExport___spec__12(x_32, x_7, x_32);
x_40 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_39);
x_41 = lean_string_append(x_38, x_40);
lean_dec(x_40);
x_42 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(x_45, x_2, x_3, x_4, x_31);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
return x_6;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Command_elabExport___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Syntax_getId(x_2);
x_8 = l_Lean_Name_append(x_1, x_7);
lean_dec(x_1);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
x_14 = l_Lean_Environment_contains(x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_free_object(x_9);
x_15 = l_Lean_Elab_Command_getRef(x_4, x_5, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_replaceRef(x_2, x_16);
lean_dec(x_16);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_4, 6);
lean_dec(x_20);
lean_ctor_set(x_4, 6, x_18);
x_21 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5(x_8, x_3, x_4, x_5, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get(x_4, 3);
x_26 = lean_ctor_get(x_4, 4);
x_27 = lean_ctor_get(x_4, 5);
x_28 = lean_ctor_get(x_4, 7);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_18);
lean_ctor_set(x_29, 7, x_28);
x_30 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5(x_8, x_3, x_29, x_5, x_17);
return x_30;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_8);
x_34 = l_Lean_Environment_contains(x_33, x_8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = l_Lean_Elab_Command_getRef(x_4, x_5, x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_replaceRef(x_2, x_36);
lean_dec(x_36);
lean_dec(x_2);
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 5);
lean_inc(x_44);
x_45 = lean_ctor_get(x_4, 7);
lean_inc(x_45);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 x_46 = x_4;
} else {
 lean_dec_ref(x_4);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 8, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_40);
lean_ctor_set(x_47, 2, x_41);
lean_ctor_set(x_47, 3, x_42);
lean_ctor_set(x_47, 4, x_43);
lean_ctor_set(x_47, 5, x_44);
lean_ctor_set(x_47, 6, x_38);
lean_ctor_set(x_47, 7, x_45);
x_48 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5(x_8, x_3, x_47, x_5, x_37);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_32);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabExport___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Command_elabExport___spec__4(x_9, x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_13, x_15);
lean_ctor_set(x_3, 1, x_17);
x_2 = x_10;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_array_push(x_12, x_19);
lean_ctor_set(x_3, 0, x_21);
x_2 = x_10;
x_7 = x_20;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_25 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Command_elabExport___spec__4(x_9, x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_push(x_24, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_2 = x_10;
x_3 = x_29;
x_7 = x_27;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_array_push(x_23, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
x_2 = x_10;
x_3 = x_34;
x_7 = x_32;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = 0;
x_8 = l_Lean_Syntax_getPos_x3f(x_6, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = 0;
x_14 = l_Lean_Syntax_getPos_x3f(x_11, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___rarg___boxed), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___rarg(x_3, x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_Exception_getRef(x_1);
x_10 = 0;
x_11 = l_Lean_Syntax_getPos_x3f(x_9, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_dec_eq(x_8, x_13);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = l_Lean_FileMap_toPosition(x_15, x_13);
lean_dec(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = l_Nat_repr(x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l_Nat_repr(x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Exception_toMessageData(x_1);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_6, 0, x_34);
return x_6;
}
else
{
lean_object* x_35; 
lean_dec(x_13);
x_35 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = l_Lean_Exception_getRef(x_1);
x_39 = 0;
x_40 = l_Lean_Syntax_getPos_x3f(x_38, x_39);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
x_41 = l_Lean_Exception_toMessageData(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_nat_dec_eq(x_36, x_43);
lean_dec(x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_45 = lean_ctor_get(x_3, 1);
x_46 = l_Lean_FileMap_toPosition(x_45, x_43);
lean_dec(x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = l_Nat_repr(x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = l_Nat_repr(x_55);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__4;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Exception_toMessageData(x_1);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_51);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_37);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_43);
x_66 = l_Lean_Exception_toMessageData(x_1);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_37);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabExport___spec__17(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_10 = lean_array_uget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15(x_10, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_12, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_7 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", errors ", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabExport___spec__17(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_toMessageList(x_11);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__9(x_19, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__3;
x_2 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__4;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_3);
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_11 = l_Lean_Syntax_getId(x_2);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__1;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 0;
x_19 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___spec__2(x_17, x_18, x_1);
x_20 = lean_array_to_list(lean_box(0), x_19);
x_21 = lean_box(0);
x_22 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_20, x_21);
x_23 = l_Lean_MessageData_ofList(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Command_getRef(x_5, x_6, x_7);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_replaceRef(x_2, x_28);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_5);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_5, 6);
lean_dec(x_32);
lean_ctor_set(x_5, 6, x_30);
x_33 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(x_26, x_4, x_5, x_6, x_29);
lean_dec(x_5);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
x_36 = lean_ctor_get(x_5, 2);
x_37 = lean_ctor_get(x_5, 3);
x_38 = lean_ctor_get(x_5, 4);
x_39 = lean_ctor_get(x_5, 5);
x_40 = lean_ctor_get(x_5, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
lean_ctor_set(x_41, 6, x_30);
lean_ctor_set(x_41, 7, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(x_26, x_4, x_41, x_6, x_29);
lean_dec(x_41);
return x_42;
}
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_5);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_8);
lean_dec(x_8);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_45 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6;
x_46 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_7);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_array_fget(x_1, x_43);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to open", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_8 = l_List_forIn_loop___at_Lean_Elab_Command_elabExport___spec__13(x_2, x_1, x_7, x_3, x_4, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_array_get_size(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_List_lengthTRAux___rarg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1(x_12, x_2, x_17, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; 
lean_dec(x_12);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_eq(x_13, x_19);
if (x_20 == 0)
{
uint8_t x_62; 
x_62 = 0;
x_21 = x_62;
goto block_61;
}
else
{
uint8_t x_63; 
x_63 = 1;
x_21 = x_63;
goto block_61;
}
block_61:
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Command_getRef(x_4, x_5, x_10);
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_13);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_replaceRef(x_2, x_23);
lean_dec(x_23);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_4, 6);
lean_dec(x_27);
lean_ctor_set(x_4, 6, x_25);
x_28 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__5;
x_29 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14(x_28, x_11, x_3, x_4, x_5, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
x_36 = lean_ctor_get(x_4, 2);
x_37 = lean_ctor_get(x_4, 3);
x_38 = lean_ctor_get(x_4, 4);
x_39 = lean_ctor_get(x_4, 5);
x_40 = lean_ctor_get(x_4, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_41 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_39);
lean_ctor_set(x_41, 6, x_25);
lean_ctor_set(x_41, 7, x_40);
x_42 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__5;
x_43 = l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14(x_42, x_11, x_3, x_41, x_5, x_24);
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
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_22);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_22, 0);
lean_dec(x_49);
x_50 = lean_nat_dec_lt(x_14, x_13);
lean_dec(x_13);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_11);
x_51 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6;
x_52 = l_panic___at___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___spec__9(x_51);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_52);
return x_22;
}
else
{
lean_object* x_53; 
x_53 = lean_array_fget(x_11, x_14);
lean_dec(x_11);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_53);
return x_22;
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_dec(x_22);
x_55 = lean_nat_dec_lt(x_14, x_13);
lean_dec(x_13);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
x_56 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6;
x_57 = l_panic___at___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___spec__9(x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_array_fget(x_11, x_14);
lean_dec(x_11);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_54);
return x_60;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___at_Lean_Elab_Command_elabExport___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = l_Lean_Elab_Command_getScope___rarg(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getScope___rarg(x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_st_mk_ref(x_14, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3(x_1, x_2, x_16, x_3, x_4, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_16, x_20);
lean_dec(x_16);
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
lean_dec(x_16);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabExport___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_5);
x_13 = l_Lean_Syntax_getId(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_14 = l_Lean_Elab_OpenDecl_resolveNameUsingNamespaces___at_Lean_Elab_Command_elabExport___spec__2(x_1, x_12, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Name_append(x_2, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_array_push(x_6, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_19;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__19(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_add_alias(x_4, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
lean_inc(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabExport___spec__18(x_2, x_3, x_10, x_12, x_13, x_14, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_6, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_array_get_size(x_16);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_16);
x_26 = lean_st_ref_set(x_6, x_19, x_20);
lean_dec(x_6);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_23, x_23);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_16);
x_34 = lean_st_ref_set(x_6, x_19, x_20);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
size_t x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_42 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__19(x_16, x_13, x_41, x_22);
lean_dec(x_16);
lean_ctor_set(x_19, 0, x_42);
x_43 = lean_st_ref_set(x_6, x_19, x_20);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
x_52 = lean_ctor_get(x_19, 2);
x_53 = lean_ctor_get(x_19, 3);
x_54 = lean_ctor_get(x_19, 4);
x_55 = lean_ctor_get(x_19, 5);
x_56 = lean_ctor_get(x_19, 6);
x_57 = lean_ctor_get(x_19, 7);
x_58 = lean_ctor_get(x_19, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_59 = lean_array_get_size(x_16);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_lt(x_60, x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_59);
lean_dec(x_16);
x_62 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_52);
lean_ctor_set(x_62, 3, x_53);
lean_ctor_set(x_62, 4, x_54);
lean_ctor_set(x_62, 5, x_55);
lean_ctor_set(x_62, 6, x_56);
lean_ctor_set(x_62, 7, x_57);
lean_ctor_set(x_62, 8, x_58);
x_63 = lean_st_ref_set(x_6, x_62, x_20);
lean_dec(x_6);
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
x_66 = lean_box(0);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_59, x_59);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_59);
lean_dec(x_16);
x_69 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_69, 0, x_50);
lean_ctor_set(x_69, 1, x_51);
lean_ctor_set(x_69, 2, x_52);
lean_ctor_set(x_69, 3, x_53);
lean_ctor_set(x_69, 4, x_54);
lean_ctor_set(x_69, 5, x_55);
lean_ctor_set(x_69, 6, x_56);
lean_ctor_set(x_69, 7, x_57);
lean_ctor_set(x_69, 8, x_58);
x_70 = lean_st_ref_set(x_6, x_69, x_20);
lean_dec(x_6);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_box(0);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_76 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__19(x_16, x_13, x_75, x_50);
lean_dec(x_16);
x_77 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_51);
lean_ctor_set(x_77, 2, x_52);
lean_ctor_set(x_77, 3, x_53);
lean_ctor_set(x_77, 4, x_54);
lean_ctor_set(x_77, 5, x_55);
lean_ctor_set(x_77, 6, x_56);
lean_ctor_set(x_77, 7, x_57);
lean_ctor_set(x_77, 8, x_58);
x_78 = lean_st_ref_set(x_6, x_77, x_20);
lean_dec(x_6);
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
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_15);
if (x_83 == 0)
{
return x_15;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_15, 0);
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_15);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid 'export', self export", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabExport___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getId(x_6);
lean_dec(x_6);
lean_inc(x_2);
x_8 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_getScope___rarg(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 2);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_9, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Command_elabExport___lambda__1(x_1, x_9, x_14, x_18, x_2, x_3, x_13);
lean_dec(x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_9);
x_20 = l_Lean_Elab_Command_elabExport___closed__2;
x_21 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_20, x_2, x_3, x_13);
lean_dec(x_3);
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
}
else
{
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 0);
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_8);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabExport___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabExport___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabExport___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getRefPos___at_Lean_Elab_Command_elabExport___spec__16(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabExport___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabExport___spec__17(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabExport___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabExport___spec__18(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Command_elabExport___spec__19(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Command_elabExport___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabExport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabExport(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("export", 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabExport", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabExport___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabExport(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(122u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(134u);
x_2 = lean_unsigned_to_nat(99u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__1;
x_2 = lean_unsigned_to_nat(31u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__2;
x_4 = lean_unsigned_to_nat(99u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(122u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(122u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__4;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__5;
x_4 = lean_unsigned_to_nat(45u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabExport_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabExport___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabOpen___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_3, x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_2, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_2, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_ResolveName_resolveNamespace(x_9, x_13, x_18, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_14);
x_20 = 1;
x_21 = l_Lean_Name_toString(x_1, x_20);
x_22 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_throwError___at_Lean_Elab_Command_elabOpen___spec__5(x_27, x_2, x_3, x_4, x_17);
return x_28;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_1);
x_32 = l_Lean_ResolveName_resolveNamespace(x_9, x_13, x_31, x_1);
lean_dec(x_13);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = 1;
x_34 = l_Lean_Name_toString(x_1, x_33);
x_35 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_throwError___at_Lean_Elab_Command_elabOpen___spec__5(x_40, x_2, x_3, x_4, x_30);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_30);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous namespace '", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: '", 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 1;
x_10 = l_Lean_Name_toString(x_1, x_9);
x_11 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2(x_7);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(x_20, x_2, x_3, x_4, x_8);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
lean_ctor_set(x_6, 0, x_25);
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_dec(x_6);
x_30 = 1;
x_31 = l_Lean_Name_toString(x_1, x_30);
x_32 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_List_toString___at_Lean_OpenDecl_instToStringOpenDecl___spec__2(x_7);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Command_elabExport___spec__11(x_41, x_2, x_3, x_4, x_29);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
return x_6;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_6);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_7, 0, x_11);
x_12 = lean_st_ref_set(x_2, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_st_ref_set(x_2, x_22, x_8);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_12, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Syntax_getId(x_16);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_18 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Command_elabExport___spec__4(x_1, x_14, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6(x_21, x_6, x_7, x_8, x_20);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_26 = lean_box(0);
x_4 = x_25;
x_5 = x_26;
x_9 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Command_elabOpen___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getSepArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__7(x_10, x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_2, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
lean_inc(x_1);
x_13 = l_Lean_Elab_OpenDecl_resolveId___at_Lean_Elab_Command_elabExport___spec__4(x_1, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_16;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Command_elabOpen___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__9(x_10, x_15, x_17, x_18, x_12, x_2, x_3, x_4, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6(x_22, x_2, x_3, x_4, x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3(x_1, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Syntax_getId(x_12);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
x_18 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6(x_17, x_6, x_7, x_8, x_15);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
x_22 = lean_box(0);
x_4 = x_21;
x_5 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Command_elabOpen___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getId(x_7);
lean_dec(x_7);
x_9 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__11(x_10, x_14, x_16, x_17, x_18, x_2, x_3, x_4, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_4);
x_13 = lean_st_ref_take(x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_1);
x_18 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_12, x_17, x_1);
lean_ctor_set(x_14, 0, x_18);
x_19 = lean_st_ref_set(x_8, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_23 = lean_box(0);
x_4 = x_22;
x_5 = x_23;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
x_27 = lean_ctor_get(x_14, 2);
x_28 = lean_ctor_get(x_14, 3);
x_29 = lean_ctor_get(x_14, 4);
x_30 = lean_ctor_get(x_14, 5);
x_31 = lean_ctor_get(x_14, 6);
x_32 = lean_ctor_get(x_14, 7);
x_33 = lean_ctor_get(x_14, 8);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
lean_inc(x_1);
x_34 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_12, x_25, x_1);
x_35 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_29);
lean_ctor_set(x_35, 5, x_30);
lean_ctor_set(x_35, 6, x_31);
lean_ctor_set(x_35, 7, x_32);
lean_ctor_set(x_35, 8, x_33);
x_36 = lean_st_ref_set(x_8, x_35, x_15);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = lean_usize_add(x_4, x_38);
x_40 = lean_box(0);
x_4 = x_39;
x_5 = x_40;
x_9 = x_37;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Command_elabOpen___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_get_size(x_8);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_box(0);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__14(x_1, x_8, x_11, x_12, x_13, x_2, x_3, x_4, x_9);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_activateScoped___at_Lean_Elab_Command_elabOpen___spec__13(x_8, x_3, x_4, x_5, x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_1 = x_9;
x_2 = x_12;
x_6 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_3);
x_12 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
x_13 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__15(x_14, x_16, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_16;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenScoped___at_Lean_Elab_Command_elabOpen___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__16(x_8, x_10, x_11, x_12, x_2, x_3, x_4, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(0);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6(x_11, x_3, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_activateScoped___at_Lean_Elab_Command_elabOpen___spec__13(x_8, x_3, x_4, x_5, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_1 = x_9;
x_2 = x_16;
x_6 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__19(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_3);
x_12 = l_Lean_Syntax_getId(x_11);
lean_dec(x_11);
x_13 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__18(x_14, x_16, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_16;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Command_elabOpen___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__19(x_8, x_10, x_11, x_12, x_2, x_3, x_4, x_5);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openSimple", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openScoped", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openOnly", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("openHiding", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_5 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 3);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__1;
lean_inc(x_1);
x_14 = l_Lean_Syntax_getKind(x_1);
x_15 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__3;
x_16 = lean_name_eq(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_12);
if (x_16 == 0)
{
uint8_t x_126; 
x_126 = 0;
x_18 = x_126;
goto block_125;
}
else
{
uint8_t x_127; 
x_127 = 1;
x_18 = x_127;
goto block_125;
}
block_125:
{
lean_object* x_19; 
x_19 = lean_st_mk_ref(x_17, x_11);
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__5;
x_23 = lean_name_eq(x_14, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__7;
x_25 = lean_name_eq(x_14, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__9;
x_27 = lean_name_eq(x_14, x_26);
lean_dec(x_14);
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_20);
x_28 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Command_elabOpen___spec__2(x_1, x_20, x_2, x_3, x_21);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_20);
x_31 = lean_apply_5(x_13, x_29, x_20, x_2, x_3, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_20, x_33);
lean_dec(x_20);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_20);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
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
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_20);
x_47 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenHiding___at_Lean_Elab_Command_elabOpen___spec__8(x_1, x_20, x_2, x_3, x_21);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_20);
x_50 = lean_apply_5(x_13, x_48, x_20, x_2, x_3, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_20, x_52);
lean_dec(x_20);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_20);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
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
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
return x_47;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_47, 0);
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_47);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_14);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_20);
x_66 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Command_elabOpen___spec__10(x_1, x_20, x_2, x_3, x_21);
lean_dec(x_1);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_20);
x_69 = lean_apply_5(x_13, x_67, x_20, x_2, x_3, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_st_ref_get(x_20, x_71);
lean_dec(x_20);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_20);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_69, 0);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_69);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_14);
x_85 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenScoped___at_Lean_Elab_Command_elabOpen___spec__12(x_1, x_20, x_2, x_3, x_21);
lean_dec(x_1);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_20);
x_88 = lean_apply_5(x_13, x_86, x_20, x_2, x_3, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_20, x_90);
lean_dec(x_20);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_20);
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
uint8_t x_100; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_85);
if (x_100 == 0)
{
return x_85;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_85, 0);
x_102 = lean_ctor_get(x_85, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_85);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_14);
x_104 = lean_ctor_get(x_19, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_19, 1);
lean_inc(x_105);
lean_dec(x_19);
x_106 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Command_elabOpen___spec__17(x_1, x_104, x_2, x_3, x_105);
lean_dec(x_1);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_104);
x_109 = lean_apply_5(x_13, x_107, x_104, x_2, x_3, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_st_ref_get(x_104, x_111);
lean_dec(x_104);
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_112, 0);
lean_dec(x_114);
lean_ctor_set(x_112, 0, x_110);
return x_112;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_104);
x_117 = !lean_is_exclusive(x_109);
if (x_117 == 0)
{
return x_109;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_109, 0);
x_119 = lean_ctor_get(x_109, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_109);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_104);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_106);
if (x_121 == 0)
{
return x_106;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_106, 0);
x_123 = lean_ctor_get(x_106, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_106);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabOpen___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 3);
lean_dec(x_4);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 4);
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_ctor_get(x_2, 6);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_1);
lean_ctor_set(x_12, 4, x_8);
lean_ctor_set(x_12, 5, x_9);
lean_ctor_set(x_12, 6, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*7, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabOpen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1(x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabOpen___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_8);
x_11 = l_Lean_Elab_Command_modifyScope(x_10, x_2, x_3, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabOpen___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at_Lean_Elab_Command_elabOpen___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_resolveNamespace___at_Lean_Elab_Command_elabOpen___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_addOpenDecl___at_Lean_Elab_Command_elabOpen___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__7(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Command_elabOpen___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenRenaming___at_Lean_Elab_Command_elabOpen___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__9(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__11(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Command_elabOpen___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenOnly___at_Lean_Elab_Command_elabOpen___spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__14(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_activateScoped___at_Lean_Elab_Command_elabOpen___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_activateScoped___at_Lean_Elab_Command_elabOpen___spec__13(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__15(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__16(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenScoped___at_Lean_Elab_Command_elabOpen___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenScoped___at_Lean_Elab_Command_elabOpen___spec__12(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Lean_Elab_Command_elabOpen___spec__18(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabOpen___spec__19(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Command_elabOpen___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_elabOpenSimple___at_Lean_Elab_Command_elabOpen___spec__17(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabOpen___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabOpen(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("open", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabOpen", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabOpen___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(136u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(138u);
x_2 = lean_unsigned_to_nat(64u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__1;
x_2 = lean_unsigned_to_nat(29u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__2;
x_4 = lean_unsigned_to_nat(64u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(136u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(136u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__4;
x_2 = lean_unsigned_to_nat(33u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__5;
x_4 = lean_unsigned_to_nat(41u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabOpen_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabOpen___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4;
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("explicitBinder", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2;
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("implicitBinder", 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2;
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4;
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__6;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_matchesNull(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_15 = lean_array_get_size(x_14);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(x_16, x_17, x_14);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Syntax_matchesNull(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_1);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Syntax_getArg(x_1, x_30);
lean_dec(x_1);
x_32 = l_Lean_Syntax_matchesNull(x_31, x_27);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_24);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(x_36, x_37, x_34);
x_39 = 1;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_1, x_6);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = lean_name_eq(x_10, x_11);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_1, x_6);
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
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to update variable binder annotation", 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
lean_inc(x_1);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_getBracketedBinderIds___spec__1(x_7, x_8, x_1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_11);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_11, x_11);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
size_t x_22; uint8_t x_23; 
x_22 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_23 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__1(x_9, x_2, x_8, x_22);
lean_dec(x_2);
lean_dec(x_9);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec(x_3);
x_24 = 0;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__2;
x_28 = l_Lean_throwError___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__2(x_27, x_3, x_4, x_5);
lean_dec(x_4);
return x_28;
}
}
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_isEqvAux___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__3(x_1, x_2, lean_box(0), x_9, x_2, x_29);
lean_dec(x_1);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_nat_dec_lt(x_29, x_11);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_11, x_11);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
return x_38;
}
else
{
size_t x_39; uint8_t x_40; 
x_39 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_40 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__4(x_9, x_2, x_8, x_39);
lean_dec(x_2);
lean_dec(x_9);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
lean_dec(x_3);
x_41 = 0;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__2;
x_45 = l_Lean_throwError___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__2(x_44, x_3, x_4, x_5);
lean_dec(x_4);
return x_45;
}
}
}
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = 1;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_5);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_getRef(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_SourceInfo_fromRef(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_SourceInfo_fromRef(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
x_3 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__7;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
x_3 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__1;
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_13 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1(x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__5;
x_21 = l_Lean_Name_str___override(x_2, x_20);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__2;
lean_inc(x_14);
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
x_25 = l_Array_append___rarg(x_24, x_3);
x_26 = lean_box(2);
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__5;
lean_inc(x_14);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6;
x_32 = lean_array_push(x_31, x_23);
x_33 = lean_array_push(x_32, x_28);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_14);
x_34 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__8;
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_array_push(x_35, x_30);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_array_push(x_7, x_37);
x_39 = lean_box(0);
x_40 = lean_box(x_6);
x_41 = lean_apply_6(x_12, x_40, x_38, x_39, x_9, x_10, x_19);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
lean_dec(x_4);
x_43 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1;
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_14);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
x_46 = lean_array_push(x_45, x_44);
x_47 = lean_array_push(x_46, x_42);
x_48 = l_Array_append___rarg(x_24, x_47);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_26);
lean_ctor_set(x_49, 1, x_27);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_array_push(x_33, x_49);
x_51 = lean_array_push(x_50, x_30);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_26);
lean_ctor_set(x_52, 1, x_21);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_array_push(x_7, x_52);
x_54 = lean_box(0);
x_55 = lean_box(x_6);
x_56 = lean_apply_6(x_12, x_55, x_53, x_54, x_9, x_10, x_19);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
x_57 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1(x_9, x_10, x_11);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__10;
lean_inc(x_58);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
x_67 = l_Array_append___rarg(x_66, x_3);
x_68 = lean_box(2);
x_69 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_67);
x_71 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__12;
lean_inc(x_58);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__13;
x_74 = lean_array_push(x_73, x_65);
x_75 = lean_array_push(x_74, x_70);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_58);
x_76 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__8;
x_77 = lean_array_push(x_75, x_76);
x_78 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11;
x_79 = lean_array_push(x_77, x_78);
x_80 = lean_array_push(x_79, x_72);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_68);
lean_ctor_set(x_81, 1, x_5);
lean_ctor_set(x_81, 2, x_80);
x_82 = lean_array_push(x_7, x_81);
x_83 = lean_box(0);
x_84 = lean_box(x_6);
x_85 = lean_apply_6(x_12, x_84, x_82, x_83, x_9, x_10, x_63);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_86 = lean_ctor_get(x_4, 0);
lean_inc(x_86);
lean_dec(x_4);
x_87 = l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1;
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_58);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
x_90 = lean_array_push(x_89, x_88);
x_91 = lean_array_push(x_90, x_86);
x_92 = l_Array_append___rarg(x_66, x_91);
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_69);
lean_ctor_set(x_93, 2, x_92);
x_94 = lean_array_push(x_75, x_93);
x_95 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11;
x_96 = lean_array_push(x_94, x_95);
x_97 = lean_array_push(x_96, x_72);
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_68);
lean_ctor_set(x_98, 1, x_5);
lean_ctor_set(x_98, 2, x_97);
x_99 = lean_array_push(x_7, x_98);
x_100 = lean_box(0);
x_101 = lean_box(x_6);
x_102 = lean_apply_6(x_12, x_101, x_99, x_100, x_9, x_10, x_63);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Syntax_getArgs(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(3u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getOptional_x3f(x_6);
lean_dec(x_6);
x_8 = l_Lean_Syntax_getArgs(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cannot update binder annotation of variables with default values/tactics", 72);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("instBinder", 10);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2;
x_2 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_30; lean_object* x_66; uint8_t x_67; 
x_12 = lean_array_uget(x_3, x_5);
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_24 = x_6;
} else {
 lean_dec_ref(x_6);
 x_24 = lean_box(0);
}
x_66 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4;
lean_inc(x_12);
x_67 = l_Lean_Syntax_isOfKind(x_12, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__6;
lean_inc(x_12);
x_69 = l_Lean_Syntax_isOfKind(x_12, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__4;
lean_inc(x_12);
x_71 = l_Lean_Syntax_isOfKind(x_12, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_box(0);
x_25 = x_72;
goto block_29;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_unsigned_to_nat(1u);
x_74 = l_Lean_Syntax_getArg(x_12, x_73);
x_75 = lean_unsigned_to_nat(2u);
lean_inc(x_74);
x_76 = l_Lean_Syntax_matchesNull(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_74);
x_77 = lean_box(0);
x_25 = x_77;
goto block_29;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_24);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Syntax_getArg(x_74, x_78);
lean_dec(x_74);
x_80 = l_Lean_Syntax_getArg(x_12, x_75);
x_81 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__5;
x_82 = lean_array_push(x_81, x_79);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_80);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
x_30 = x_86;
goto block_65;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_unsigned_to_nat(1u);
x_88 = l_Lean_Syntax_getArg(x_12, x_87);
x_89 = lean_unsigned_to_nat(2u);
x_90 = l_Lean_Syntax_getArg(x_12, x_89);
x_91 = l_Lean_Syntax_isNone(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_inc(x_90);
x_92 = l_Lean_Syntax_matchesNull(x_90, x_89);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_90);
lean_dec(x_88);
x_93 = lean_box(0);
x_25 = x_93;
goto block_29;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_24);
x_94 = l_Lean_Syntax_getArg(x_90, x_87);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_box(0);
x_97 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__3(x_88, x_96, x_95);
lean_dec(x_88);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_30 = x_98;
goto block_65;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_90);
lean_dec(x_24);
x_99 = lean_box(0);
x_100 = lean_box(0);
x_101 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__3(x_88, x_100, x_99);
lean_dec(x_88);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_30 = x_102;
goto block_65;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = l_Lean_Syntax_getArg(x_12, x_103);
x_105 = lean_unsigned_to_nat(2u);
x_106 = l_Lean_Syntax_getArg(x_12, x_105);
x_107 = l_Lean_Syntax_isNone(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_inc(x_106);
x_108 = l_Lean_Syntax_matchesNull(x_106, x_105);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_106);
lean_dec(x_104);
x_109 = lean_box(0);
x_25 = x_109;
goto block_29;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_24);
x_110 = l_Lean_Syntax_getArg(x_106, x_103);
lean_dec(x_106);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_box(0);
x_113 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__4(x_12, x_104, x_112, x_111);
lean_dec(x_104);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_30 = x_114;
goto block_65;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_106);
lean_dec(x_24);
x_115 = lean_box(0);
x_116 = lean_box(0);
x_117 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__4(x_12, x_104, x_116, x_115);
lean_dec(x_104);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec(x_117);
x_30 = x_118;
goto block_65;
}
}
block_21:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_6 = x_17;
x_9 = x_14;
goto _start;
}
}
block_29:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
x_26 = lean_array_push(x_23, x_12);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_13 = x_28;
x_14 = x_9;
goto block_21;
}
block_65:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_32);
x_35 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames(x_32, x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_array_push(x_23, x_12);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_13 = x_41;
x_14 = x_38;
goto block_21;
}
else
{
lean_dec(x_12);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2;
x_44 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4;
x_45 = lean_box(0);
x_46 = lean_unbox(x_22);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
x_47 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2(x_2, x_43, x_32, x_33, x_44, x_46, x_23, x_45, x_7, x_8, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_13 = x_48;
x_14 = x_49;
goto block_21;
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 0);
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_dec(x_35);
x_55 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__2;
x_56 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_55, x_7, x_8, x_54);
lean_dec(x_8);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_35);
if (x_61 == 0)
{
return x_35;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_35, 0);
x_63 = lean_ctor_get(x_35, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_35);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 5);
lean_dec(x_4);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_ctor_get(x_2, 4);
x_10 = lean_ctor_get(x_2, 6);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_7);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set(x_12, 5, x_1);
lean_ctor_set(x_12, 6, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*7, x_11);
return x_12;
}
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f(x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 5);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___closed__1;
x_20 = lean_unbox(x_11);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2(x_10, x_20, x_15, x_17, x_18, x_19, x_2, x_3, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
lean_dec(x_26);
x_27 = 0;
x_28 = lean_box(x_27);
lean_ctor_set(x_21, 0, x_28);
return x_21;
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___lambda__1), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = l_Lean_Elab_Command_modifyScope(x_35, x_2, x_3, x_33);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = 1;
x_40 = lean_box(x_39);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = 1;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_21, 0);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_21);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__1(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2(x_12, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2(x_1, x_10, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadQuotation_addMacroScope___at_Lean_Elab_Command_elabVariable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_addMacroScope(x_6, x_1, x_10);
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
x_14 = l_Lean_addMacroScope(x_6, x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_4, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_uget(x_5, x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_5, x_4, x_12);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_11);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_15 = lean_apply_4(x_1, x_14, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_20 = lean_array_uset(x_13, x_4, x_16);
x_4 = x_19;
x_5 = x_20;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___at_Lean_Elab_Command_elabVariable___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_MonadQuotation_addMacroScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed), 4, 1);
lean_closure_set(x_12, 0, x_9);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Command_withFreshMacroScope___rarg(x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_11, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
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
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 5);
x_6 = lean_ctor_get(x_3, 6);
x_7 = lean_array_push(x_5, x_1);
x_8 = l_Array_append___rarg(x_6, x_2);
lean_ctor_set(x_3, 6, x_8);
lean_ctor_set(x_3, 5, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 2);
x_12 = lean_ctor_get(x_3, 3);
x_13 = lean_ctor_get(x_3, 4);
x_14 = lean_ctor_get(x_3, 5);
x_15 = lean_ctor_get(x_3, 6);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_17 = lean_array_push(x_14, x_1);
x_18 = l_Array_append___rarg(x_15, x_2);
x_19 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_13);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_19, 6, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_11 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation(x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_10);
x_15 = l_Lean_Elab_Command_getBracketedBinderIds(x_10);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___at_Lean_Elab_Command_elabVariable___spec__3(x_17, x_18, x_15, x_5, x_6, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4___lambda__1), 3, 2);
lean_closure_set(x_22, 0, x_10);
lean_closure_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_Command_modifyScope(x_22, x_5, x_6, x_21);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = lean_usize_add(x_3, x_25);
x_27 = lean_box(0);
x_3 = x_26;
x_4 = x_27;
x_7 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
lean_dec(x_10);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_36 = lean_box(0);
x_3 = x_35;
x_4 = x_36;
x_7 = x_33;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabVariable___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Command_elabVariable___lambda__2___closed__1;
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabVariable___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_11, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_17 = l_Array_toSubarray___rarg(x_3, x_16, x_15);
x_18 = lean_ctor_get(x_1, 6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_array_get_size(x_18);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_18, x_21, x_22, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_4, 6);
lean_dec(x_28);
lean_ctor_set(x_4, 6, x_26);
x_29 = l_Lean_Core_resetMessageLog(x_8, x_9, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__2___boxed), 10, 1);
lean_closure_set(x_31, 0, x_2);
x_32 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_33 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_3, x_32, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
x_36 = lean_ctor_get(x_4, 2);
x_37 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_38 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
x_39 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_40 = lean_ctor_get(x_4, 3);
x_41 = lean_ctor_get(x_4, 4);
x_42 = lean_ctor_get(x_4, 5);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 3);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 4);
x_45 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 5);
x_46 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 6);
x_47 = lean_ctor_get(x_4, 7);
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 7);
lean_inc(x_47);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_49 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_35);
lean_ctor_set(x_49, 2, x_36);
lean_ctor_set(x_49, 3, x_40);
lean_ctor_set(x_49, 4, x_41);
lean_ctor_set(x_49, 5, x_42);
lean_ctor_set(x_49, 6, x_26);
lean_ctor_set(x_49, 7, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*8, x_37);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 1, x_38);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 2, x_39);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 3, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 4, x_44);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 5, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 6, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 7, x_48);
x_50 = l_Lean_Core_resetMessageLog(x_8, x_9, x_25);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__2___boxed), 10, 1);
lean_closure_set(x_52, 0, x_2);
x_53 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_54 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_3, x_53, x_52, x_49, x_5, x_6, x_7, x_8, x_9, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("variable", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabVariable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabVariable___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabVariable___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Elab_Command_getScope___rarg(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 5);
lean_inc(x_15);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable___lambda__3___boxed), 10, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_18, 0, x_17);
lean_inc(x_2);
x_19 = l_Lean_Elab_Command_liftTermElabM___rarg(x_11, x_18, x_2, x_3, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_get_size(x_10);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4(x_10, x_22, x_23, x_24, x_2, x_3, x_20);
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
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
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
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadQuotation_addMacroScope___at_Lean_Elab_Command_elabVariable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadQuotation_addMacroScope___at_Lean_Elab_Command_elabVariable___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2(x_1, x_2, x_9, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___at_Lean_Elab_Command_elabVariable___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabVariable___spec__2___at_Lean_Elab_Command_elabVariable___spec__3(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabVariable___spec__4(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabVariable___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabVariable___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabVariable___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabVariable___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabVariable", 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabVariable), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabVariable___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(209u);
x_2 = lean_unsigned_to_nat(33u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(218u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__1;
x_2 = lean_unsigned_to_nat(33u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(209u);
x_2 = lean_unsigned_to_nat(37u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(209u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__4;
x_2 = lean_unsigned_to_nat(37u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__5;
x_4 = lean_unsigned_to_nat(49u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabVariable_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Command_elabCheckCore___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckCore___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" : ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_12, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_16, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1;
x_24 = l_Lean_Elab_Term_levelMVarToParam(x_20, x_22, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_27);
x_28 = lean_infer_type(x_27, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_Expr_isSyntheticSorry(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_free_object(x_28);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_27);
x_34 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_30);
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
x_41 = 0;
x_42 = l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_4, x_40, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_43 = lean_box(0);
lean_ctor_set(x_28, 0, x_43);
return x_28;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = l_Lean_Expr_isSyntheticSorry(x_27);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_27);
x_48 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__3;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_44);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
x_55 = 0;
x_56 = l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_4, x_54, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_45);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_27);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
return x_28;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_28, 0);
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_28);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_17);
if (x_63 == 0)
{
return x_17;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_17, 0);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_17);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_13);
if (x_67 == 0)
{
return x_13;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_13, 0);
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_13);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_box(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckCore___lambda__2___boxed), 11, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_3);
x_16 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_13, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_array_get_size(x_5);
x_18 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_19 = l_Array_toSubarray___rarg(x_5, x_18, x_17);
x_20 = lean_ctor_get(x_1, 6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_array_get_size(x_20);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_20, x_23, x_24, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_6, 6);
lean_dec(x_30);
lean_ctor_set(x_6, 6, x_28);
x_31 = l_Lean_Core_resetMessageLog(x_10, x_11, x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(x_3);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckCore___lambda__3___boxed), 12, 3);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_33);
lean_closure_set(x_34, 2, x_4);
x_35 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_36 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_5, x_35, x_34, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_6, 2);
x_40 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
x_41 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 1);
x_42 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 2);
x_43 = lean_ctor_get(x_6, 3);
x_44 = lean_ctor_get(x_6, 4);
x_45 = lean_ctor_get(x_6, 5);
x_46 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 3);
x_47 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 4);
x_48 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 5);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
x_50 = lean_ctor_get(x_6, 7);
x_51 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 7);
lean_inc(x_50);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_52 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_38);
lean_ctor_set(x_52, 2, x_39);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set(x_52, 4, x_44);
lean_ctor_set(x_52, 5, x_45);
lean_ctor_set(x_52, 6, x_28);
lean_ctor_set(x_52, 7, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*8, x_40);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 1, x_41);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 2, x_42);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 3, x_46);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 4, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 5, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 6, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 7, x_51);
x_53 = l_Lean_Core_resetMessageLog(x_10, x_11, x_27);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(x_3);
x_56 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckCore___lambda__3___boxed), 12, 3);
lean_closure_set(x_56, 0, x_2);
lean_closure_set(x_56, 1, x_55);
lean_closure_set(x_56, 2, x_4);
x_57 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_58 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_5, x_57, x_56, x_52, x_7, x_8, x_9, x_10, x_11, x_54);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_14);
if (x_59 == 0)
{
return x_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_14, 0);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_14);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("check", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabCheckCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_check", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabCheckCore___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabCheckCore___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_Command_elabCheckCore___closed__2;
lean_inc(x_2);
x_7 = l_Lean_Syntax_isOfKind(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_2, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
lean_dec(x_2);
x_13 = lean_st_ref_get(x_4, x_5);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_getScope___rarg(x_4, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 5);
lean_inc(x_20);
x_21 = lean_box(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckCore___lambda__4___boxed), 12, 4);
lean_closure_set(x_22, 0, x_18);
lean_closure_set(x_22, 1, x_12);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_10);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_23, 0, x_20);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_Command_elabCheckCore___closed__5;
lean_inc(x_3);
x_26 = l_Lean_Elab_Command_liftTermElabM___rarg(x_25, x_24, x_3, x_4, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_16, x_3, x_4, x_28);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_16, x_3, x_4, x_35);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_elabCheckCore___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_Command_elabCheckCore___lambda__2(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_Command_elabCheckCore___lambda__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_Command_elabCheckCore___lambda__4(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Command_elabCheckCore(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Elab_Command_elabCheckCore(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabCheck(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabCheck", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheck___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabCheckCore___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(232u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(232u);
x_2 = lean_unsigned_to_nat(116u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__1;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__2;
x_4 = lean_unsigned_to_nat(116u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(232u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(232u);
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__4;
x_2 = lean_unsigned_to_nat(52u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__5;
x_4 = lean_unsigned_to_nat(61u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheck_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabReduce___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("smartUnfolding", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabReduce___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabReduce___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_11, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_15, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1;
x_23 = l_Lean_Elab_Term_levelMVarToParam(x_19, x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_ctor_get(x_8, 2);
x_29 = l_Lean_Elab_Command_elabReduce___lambda__1___closed__2;
x_30 = l_Lean_KVMap_setBool(x_28, x_29, x_15);
lean_ctor_set(x_8, 2, x_30);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_6, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_6, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_6, 5);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 0;
lean_ctor_set_uint8(x_31, 5, x_38);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_35);
lean_ctor_set(x_39, 5, x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = l_Lean_Meta_reduce(x_26, x_11, x_15, x_15, x_39, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = 0;
x_45 = l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_3, x_43, x_44, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_ctor_get_uint8(x_31, 0);
x_51 = lean_ctor_get_uint8(x_31, 1);
x_52 = lean_ctor_get_uint8(x_31, 2);
x_53 = lean_ctor_get_uint8(x_31, 3);
x_54 = lean_ctor_get_uint8(x_31, 4);
x_55 = lean_ctor_get_uint8(x_31, 6);
x_56 = lean_ctor_get_uint8(x_31, 7);
x_57 = lean_ctor_get_uint8(x_31, 8);
x_58 = lean_ctor_get_uint8(x_31, 9);
x_59 = lean_ctor_get_uint8(x_31, 10);
x_60 = lean_ctor_get_uint8(x_31, 11);
x_61 = lean_ctor_get_uint8(x_31, 12);
x_62 = lean_ctor_get_uint8(x_31, 13);
lean_dec(x_31);
x_63 = 0;
x_64 = lean_alloc_ctor(0, 0, 14);
lean_ctor_set_uint8(x_64, 0, x_50);
lean_ctor_set_uint8(x_64, 1, x_51);
lean_ctor_set_uint8(x_64, 2, x_52);
lean_ctor_set_uint8(x_64, 3, x_53);
lean_ctor_set_uint8(x_64, 4, x_54);
lean_ctor_set_uint8(x_64, 5, x_63);
lean_ctor_set_uint8(x_64, 6, x_55);
lean_ctor_set_uint8(x_64, 7, x_56);
lean_ctor_set_uint8(x_64, 8, x_57);
lean_ctor_set_uint8(x_64, 9, x_58);
lean_ctor_set_uint8(x_64, 10, x_59);
lean_ctor_set_uint8(x_64, 11, x_60);
lean_ctor_set_uint8(x_64, 12, x_61);
lean_ctor_set_uint8(x_64, 13, x_62);
x_65 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_32);
lean_ctor_set(x_65, 2, x_33);
lean_ctor_set(x_65, 3, x_34);
lean_ctor_set(x_65, 4, x_35);
lean_ctor_set(x_65, 5, x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_66 = l_Lean_Meta_reduce(x_26, x_11, x_15, x_15, x_65, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_67);
x_70 = 0;
x_71 = l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_3, x_69, x_70, x_4, x_5, x_6, x_7, x_8, x_9, x_68);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
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
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_76 = lean_ctor_get(x_8, 0);
x_77 = lean_ctor_get(x_8, 1);
x_78 = lean_ctor_get(x_8, 2);
x_79 = lean_ctor_get(x_8, 3);
x_80 = lean_ctor_get(x_8, 4);
x_81 = lean_ctor_get(x_8, 5);
x_82 = lean_ctor_get(x_8, 6);
x_83 = lean_ctor_get(x_8, 7);
x_84 = lean_ctor_get(x_8, 8);
x_85 = lean_ctor_get(x_8, 9);
x_86 = lean_ctor_get(x_8, 10);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_8);
x_87 = l_Lean_Elab_Command_elabReduce___lambda__1___closed__2;
x_88 = l_Lean_KVMap_setBool(x_78, x_87, x_15);
x_89 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_77);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_79);
lean_ctor_set(x_89, 4, x_80);
lean_ctor_set(x_89, 5, x_81);
lean_ctor_set(x_89, 6, x_82);
lean_ctor_set(x_89, 7, x_83);
lean_ctor_set(x_89, 8, x_84);
lean_ctor_set(x_89, 9, x_85);
lean_ctor_set(x_89, 10, x_86);
x_90 = lean_ctor_get(x_6, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_6, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_6, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_6, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_6, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_6, 5);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_90, 0);
x_97 = lean_ctor_get_uint8(x_90, 1);
x_98 = lean_ctor_get_uint8(x_90, 2);
x_99 = lean_ctor_get_uint8(x_90, 3);
x_100 = lean_ctor_get_uint8(x_90, 4);
x_101 = lean_ctor_get_uint8(x_90, 6);
x_102 = lean_ctor_get_uint8(x_90, 7);
x_103 = lean_ctor_get_uint8(x_90, 8);
x_104 = lean_ctor_get_uint8(x_90, 9);
x_105 = lean_ctor_get_uint8(x_90, 10);
x_106 = lean_ctor_get_uint8(x_90, 11);
x_107 = lean_ctor_get_uint8(x_90, 12);
x_108 = lean_ctor_get_uint8(x_90, 13);
if (lean_is_exclusive(x_90)) {
 x_109 = x_90;
} else {
 lean_dec_ref(x_90);
 x_109 = lean_box(0);
}
x_110 = 0;
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 0, 14);
} else {
 x_111 = x_109;
}
lean_ctor_set_uint8(x_111, 0, x_96);
lean_ctor_set_uint8(x_111, 1, x_97);
lean_ctor_set_uint8(x_111, 2, x_98);
lean_ctor_set_uint8(x_111, 3, x_99);
lean_ctor_set_uint8(x_111, 4, x_100);
lean_ctor_set_uint8(x_111, 5, x_110);
lean_ctor_set_uint8(x_111, 6, x_101);
lean_ctor_set_uint8(x_111, 7, x_102);
lean_ctor_set_uint8(x_111, 8, x_103);
lean_ctor_set_uint8(x_111, 9, x_104);
lean_ctor_set_uint8(x_111, 10, x_105);
lean_ctor_set_uint8(x_111, 11, x_106);
lean_ctor_set_uint8(x_111, 12, x_107);
lean_ctor_set_uint8(x_111, 13, x_108);
x_112 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_91);
lean_ctor_set(x_112, 2, x_92);
lean_ctor_set(x_112, 3, x_93);
lean_ctor_set(x_112, 4, x_94);
lean_ctor_set(x_112, 5, x_95);
lean_inc(x_9);
lean_inc(x_89);
lean_inc(x_7);
x_113 = l_Lean_Meta_reduce(x_26, x_11, x_15, x_15, x_112, x_7, x_89, x_9, x_25);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_117 = 0;
x_118 = l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_3, x_116, x_117, x_4, x_5, x_6, x_7, x_89, x_9, x_115);
lean_dec(x_9);
lean_dec(x_89);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_89);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
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
else
{
uint8_t x_123; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_123 = !lean_is_exclusive(x_16);
if (x_123 == 0)
{
return x_16;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_16, 0);
x_125 = lean_ctor_get(x_16, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_16);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_127 = !lean_is_exclusive(x_12);
if (x_127 == 0)
{
return x_12;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_12, 0);
x_129 = lean_ctor_get(x_12, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_12);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___lambda__1___boxed), 10, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_2);
x_14 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_12, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_array_get_size(x_4);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_18 = l_Array_toSubarray___rarg(x_4, x_17, x_16);
x_19 = lean_ctor_get(x_1, 6);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_array_get_size(x_19);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_19, x_22, x_23, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_5, 6);
lean_dec(x_29);
lean_ctor_set(x_5, 6, x_27);
x_30 = l_Lean_Core_resetMessageLog(x_9, x_10, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___lambda__2___boxed), 11, 2);
lean_closure_set(x_32, 0, x_2);
lean_closure_set(x_32, 1, x_3);
x_33 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_34 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_4, x_33, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
x_37 = lean_ctor_get(x_5, 2);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_39 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
x_41 = lean_ctor_get(x_5, 3);
x_42 = lean_ctor_get(x_5, 4);
x_43 = lean_ctor_get(x_5, 5);
x_44 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 3);
x_45 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 4);
x_46 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 5);
x_47 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 6);
x_48 = lean_ctor_get(x_5, 7);
x_49 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 7);
lean_inc(x_48);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
x_50 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set(x_50, 2, x_37);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_43);
lean_ctor_set(x_50, 6, x_27);
lean_ctor_set(x_50, 7, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*8, x_38);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 1, x_39);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 2, x_40);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 3, x_44);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 4, x_45);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 5, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 6, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 7, x_49);
x_51 = l_Lean_Core_resetMessageLog(x_9, x_10, x_26);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___lambda__2___boxed), 11, 2);
lean_closure_set(x_53, 0, x_2);
lean_closure_set(x_53, 1, x_3);
x_54 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_55 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_4, x_54, x_53, x_50, x_6, x_7, x_8, x_9, x_10, x_52);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabReduce___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("reduce", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabReduce___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabReduce___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabReduce___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_st_ref_get(x_3, x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Command_getScope___rarg(x_3, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 5);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___lambda__3___boxed), 11, 3);
lean_closure_set(x_20, 0, x_17);
lean_closure_set(x_20, 1, x_11);
lean_closure_set(x_20, 2, x_9);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = l_Lean_Elab_Command_elabCheckCore___closed__5;
lean_inc(x_2);
x_24 = l_Lean_Elab_Command_liftTermElabM___rarg(x_23, x_22, x_2, x_3, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_15, x_2, x_3, x_26);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_15, x_2, x_3, x_33);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabReduce___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabReduce___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabReduce___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabReduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabReduce(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabReduce", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabReduce___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabReduce___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabReduce___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabReduce___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(234u);
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(243u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__1;
x_2 = lean_unsigned_to_nat(49u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(234u);
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(234u);
x_2 = lean_unsigned_to_nat(63u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__4;
x_2 = lean_unsigned_to_nat(53u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__5;
x_4 = lean_unsigned_to_nat(63u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabReduce_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabReduce___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_6);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
x_9 = lean_box(x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_hasNoErrorMessages___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_hasNoErrorMessages(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected success", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2;
x_8 = l_Lean_throwError___at___private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing___spec__1(x_7, x_2, x_3, x_4);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_failIfSucceeds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_failIfSucceeds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_take(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_48; lean_object* x_49; lean_object* x_79; 
x_13 = lean_ctor_get(x_10, 1);
lean_dec(x_13);
x_14 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3;
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_st_ref_set(x_3, x_10, x_11);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_79 = lean_apply_3(x_1, x_2, x_3, x_16);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_3, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_unbox(x_82);
lean_dec(x_82);
x_18 = x_84;
x_19 = x_83;
goto block_47;
}
else
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
lean_inc(x_3);
lean_inc(x_2);
x_87 = l_Lean_Elab_logException___at_Lean_Elab_Command_elabCommand___spec__3(x_85, x_2, x_3, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = 0;
x_18 = x_89;
x_19 = x_88;
goto block_47;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_2);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_48 = x_90;
x_49 = x_91;
goto block_78;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_79, 1);
lean_inc(x_92);
lean_dec(x_79);
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_85, 0);
x_95 = lean_ctor_get(x_85, 1);
lean_dec(x_95);
x_96 = l_Lean_InternalExceptionId_getName(x_94, x_92);
lean_dec(x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_free_object(x_85);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_97);
x_100 = 2;
lean_inc(x_3);
lean_inc(x_2);
x_101 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_99, x_100, x_2, x_3, x_98);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = 0;
x_18 = x_103;
x_19 = x_102;
goto block_47;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_96, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_96, 1);
lean_inc(x_105);
lean_dec(x_96);
x_106 = lean_ctor_get(x_2, 6);
lean_inc(x_106);
lean_dec(x_2);
x_107 = lean_io_error_to_string(x_104);
x_108 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set_tag(x_85, 0);
lean_ctor_set(x_85, 1, x_109);
lean_ctor_set(x_85, 0, x_106);
x_48 = x_85;
x_49 = x_105;
goto block_78;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_85, 0);
lean_inc(x_110);
lean_dec(x_85);
x_111 = l_Lean_InternalExceptionId_getName(x_110, x_92);
lean_dec(x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_114, 0, x_112);
x_115 = 2;
lean_inc(x_3);
lean_inc(x_2);
x_116 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_114, x_115, x_2, x_3, x_113);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = 0;
x_18 = x_118;
x_19 = x_117;
goto block_47;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_dec(x_111);
x_121 = lean_ctor_get(x_2, 6);
lean_inc(x_121);
lean_dec(x_2);
x_122 = lean_io_error_to_string(x_119);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_48 = x_125;
x_49 = x_120;
goto block_78;
}
}
}
}
block_47:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_3, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_24);
x_26 = l_Std_PersistentArray_append___rarg(x_8, x_25);
lean_ctor_set(x_21, 1, x_26);
x_27 = lean_st_ref_set(x_3, x_21, x_22);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(x_18);
x_30 = lean_apply_4(x_17, x_29, x_2, x_3, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
x_33 = lean_ctor_get(x_21, 2);
x_34 = lean_ctor_get(x_21, 3);
x_35 = lean_ctor_get(x_21, 4);
x_36 = lean_ctor_get(x_21, 5);
x_37 = lean_ctor_get(x_21, 6);
x_38 = lean_ctor_get(x_21, 7);
x_39 = lean_ctor_get(x_21, 8);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_40 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_32);
x_41 = l_Std_PersistentArray_append___rarg(x_8, x_40);
x_42 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_33);
lean_ctor_set(x_42, 3, x_34);
lean_ctor_set(x_42, 4, x_35);
lean_ctor_set(x_42, 5, x_36);
lean_ctor_set(x_42, 6, x_37);
lean_ctor_set(x_42, 7, x_38);
lean_ctor_set(x_42, 8, x_39);
x_43 = lean_st_ref_set(x_3, x_42, x_22);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(x_18);
x_46 = lean_apply_4(x_17, x_45, x_2, x_3, x_44);
return x_46;
}
}
block_78:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_st_ref_take(x_3, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_51, 1);
x_55 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_54);
x_56 = l_Std_PersistentArray_append___rarg(x_8, x_55);
lean_ctor_set(x_51, 1, x_56);
x_57 = lean_st_ref_set(x_3, x_51, x_52);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set_tag(x_57, 1);
lean_ctor_set(x_57, 0, x_48);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
x_64 = lean_ctor_get(x_51, 2);
x_65 = lean_ctor_get(x_51, 3);
x_66 = lean_ctor_get(x_51, 4);
x_67 = lean_ctor_get(x_51, 5);
x_68 = lean_ctor_get(x_51, 6);
x_69 = lean_ctor_get(x_51, 7);
x_70 = lean_ctor_get(x_51, 8);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_71 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_63);
x_72 = l_Std_PersistentArray_append___rarg(x_8, x_71);
x_73 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_64);
lean_ctor_set(x_73, 3, x_65);
lean_ctor_set(x_73, 4, x_66);
lean_ctor_set(x_73, 5, x_67);
lean_ctor_set(x_73, 6, x_68);
lean_ctor_set(x_73, 7, x_69);
lean_ctor_set(x_73, 8, x_70);
x_74 = lean_st_ref_set(x_3, x_73, x_52);
lean_dec(x_3);
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
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_48);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_162; lean_object* x_163; lean_object* x_185; 
x_126 = lean_ctor_get(x_10, 0);
x_127 = lean_ctor_get(x_10, 2);
x_128 = lean_ctor_get(x_10, 3);
x_129 = lean_ctor_get(x_10, 4);
x_130 = lean_ctor_get(x_10, 5);
x_131 = lean_ctor_get(x_10, 6);
x_132 = lean_ctor_get(x_10, 7);
x_133 = lean_ctor_get(x_10, 8);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_10);
x_134 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3;
x_135 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_127);
lean_ctor_set(x_135, 3, x_128);
lean_ctor_set(x_135, 4, x_129);
lean_ctor_set(x_135, 5, x_130);
lean_ctor_set(x_135, 6, x_131);
lean_ctor_set(x_135, 7, x_132);
lean_ctor_set(x_135, 8, x_133);
x_136 = lean_st_ref_set(x_3, x_135, x_11);
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_Lean_Elab_Command_failIfSucceeds___closed__1;
lean_inc(x_3);
lean_inc(x_2);
x_185 = lean_apply_3(x_1, x_2, x_3, x_137);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = l_Lean_Elab_Command_hasNoErrorMessages___rarg(x_3, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_unbox(x_188);
lean_dec(x_188);
x_139 = x_190;
x_140 = x_189;
goto block_161;
}
else
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_185, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_185, 1);
lean_inc(x_192);
lean_dec(x_185);
lean_inc(x_3);
lean_inc(x_2);
x_193 = l_Lean_Elab_logException___at_Lean_Elab_Command_elabCommand___spec__3(x_191, x_2, x_3, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = 0;
x_139 = x_195;
x_140 = x_194;
goto block_161;
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_2);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
lean_dec(x_193);
x_162 = x_196;
x_163 = x_197;
goto block_184;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_185, 1);
lean_inc(x_198);
lean_dec(x_185);
x_199 = lean_ctor_get(x_191, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_200 = x_191;
} else {
 lean_dec_ref(x_191);
 x_200 = lean_box(0);
}
x_201 = l_Lean_InternalExceptionId_getName(x_199, x_198);
lean_dec(x_199);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_dec(x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_204, 0, x_202);
x_205 = 2;
lean_inc(x_3);
lean_inc(x_2);
x_206 = l_Lean_log___at_Lean_Elab_Command_elabCommand___spec__5(x_204, x_205, x_2, x_3, x_203);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_208 = 0;
x_139 = x_208;
x_140 = x_207;
goto block_161;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_201, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_201, 1);
lean_inc(x_210);
lean_dec(x_201);
x_211 = lean_ctor_get(x_2, 6);
lean_inc(x_211);
lean_dec(x_2);
x_212 = lean_io_error_to_string(x_209);
x_213 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_213);
if (lean_is_scalar(x_200)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_200;
 lean_ctor_set_tag(x_215, 0);
}
lean_ctor_set(x_215, 0, x_211);
lean_ctor_set(x_215, 1, x_214);
x_162 = x_215;
x_163 = x_210;
goto block_184;
}
}
}
block_161:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_141 = lean_st_ref_take(x_3, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_ctor_get(x_142, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_142, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_142, 3);
lean_inc(x_147);
x_148 = lean_ctor_get(x_142, 4);
lean_inc(x_148);
x_149 = lean_ctor_get(x_142, 5);
lean_inc(x_149);
x_150 = lean_ctor_get(x_142, 6);
lean_inc(x_150);
x_151 = lean_ctor_get(x_142, 7);
lean_inc(x_151);
x_152 = lean_ctor_get(x_142, 8);
lean_inc(x_152);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 lean_ctor_release(x_142, 2);
 lean_ctor_release(x_142, 3);
 lean_ctor_release(x_142, 4);
 lean_ctor_release(x_142, 5);
 lean_ctor_release(x_142, 6);
 lean_ctor_release(x_142, 7);
 lean_ctor_release(x_142, 8);
 x_153 = x_142;
} else {
 lean_dec_ref(x_142);
 x_153 = lean_box(0);
}
x_154 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_145);
x_155 = l_Std_PersistentArray_append___rarg(x_8, x_154);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 9, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_144);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_156, 2, x_146);
lean_ctor_set(x_156, 3, x_147);
lean_ctor_set(x_156, 4, x_148);
lean_ctor_set(x_156, 5, x_149);
lean_ctor_set(x_156, 6, x_150);
lean_ctor_set(x_156, 7, x_151);
lean_ctor_set(x_156, 8, x_152);
x_157 = lean_st_ref_set(x_3, x_156, x_143);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_box(x_139);
x_160 = lean_apply_4(x_138, x_159, x_2, x_3, x_158);
return x_160;
}
block_184:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_164 = lean_st_ref_take(x_3, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_165, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_165, 5);
lean_inc(x_172);
x_173 = lean_ctor_get(x_165, 6);
lean_inc(x_173);
x_174 = lean_ctor_get(x_165, 7);
lean_inc(x_174);
x_175 = lean_ctor_get(x_165, 8);
lean_inc(x_175);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 lean_ctor_release(x_165, 4);
 lean_ctor_release(x_165, 5);
 lean_ctor_release(x_165, 6);
 lean_ctor_release(x_165, 7);
 lean_ctor_release(x_165, 8);
 x_176 = x_165;
} else {
 lean_dec_ref(x_165);
 x_176 = lean_box(0);
}
x_177 = l_Std_PersistentArray_mapM___at_Lean_MessageLog_errorsToWarnings___spec__1(x_168);
x_178 = l_Std_PersistentArray_append___rarg(x_8, x_177);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 9, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_167);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_169);
lean_ctor_set(x_179, 3, x_170);
lean_ctor_set(x_179, 4, x_171);
lean_ctor_set(x_179, 5, x_172);
lean_ctor_set(x_179, 6, x_173);
lean_ctor_set(x_179, 7, x_174);
lean_ctor_set(x_179, 8, x_175);
x_180 = lean_st_ref_set(x_3, x_179, x_166);
lean_dec(x_3);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
 lean_ctor_set_tag(x_183, 1);
}
lean_ctor_set(x_183, 0, x_162);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_failIfSucceeds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Command_failIfSucceeds___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("check_failure", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckFailure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabCheckFailure___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCheckFailure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#check", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCheckFailure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabCheckFailure___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__1(x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_getMainModule___rarg(x_3, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Command_elabCheckFailure___closed__3;
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_array_push(x_20, x_9);
x_22 = lean_box(2);
x_23 = l_Lean_Elab_Command_elabCheckCore___closed__2;
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckCore___boxed), 5, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_24);
x_28 = l_Lean_Elab_Command_failIfSucceeds(x_27, x_2, x_3, x_16);
return x_28;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabCheckFailure", 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCheckFailure), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabCheckFailure___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(268u);
x_2 = lean_unsigned_to_nat(38u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(271u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__1;
x_2 = lean_unsigned_to_nat(38u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(268u);
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(268u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__4;
x_2 = lean_unsigned_to_nat(42u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__5;
x_4 = lean_unsigned_to_nat(58u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expression", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nhas type", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nbut instance", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nfailed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `", 167);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("` class", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_11 = l_Lean_Meta_getDecLevel(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_1);
x_16 = l_Lean_Expr_const___override(x_1, x_15);
lean_inc(x_9);
lean_inc(x_16);
x_17 = l_Lean_Expr_app___override(x_16, x_9);
x_18 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_17);
x_19 = l_Lean_Meta_synthInstance(x_17, x_18, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_68; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_68 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_16);
x_71 = l_Lean_Expr_app___override(x_16, x_69);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_72 = l_Lean_Meta_synthInstance(x_71, x_18, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_72;
}
else
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_21 = x_73;
goto block_67;
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_21 = x_74;
goto block_67;
}
block_67:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = 1;
x_23 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_24 = l_Lean_Meta_reduce(x_9, x_22, x_23, x_22, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Expr_app___override(x_16, x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_Meta_synthInstance(x_27, x_18, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_indentExpr(x_2);
x_31 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_indentExpr(x_9);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__6;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_indentExpr(x_17);
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__8;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_1);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__10;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_46, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_16);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_dec(x_24);
x_49 = l_Lean_indentExpr(x_2);
x_50 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__2;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__4;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_9);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__6;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_indentExpr(x_17);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__8;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_62, 0, x_1);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__10;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_65, x_3, x_4, x_5, x_6, x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_66;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_11);
if (x_75 == 0)
{
return x_11;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_11, 0);
x_77 = lean_ctor_get(x_11, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_11);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_8);
if (x_79 == 0)
{
return x_8;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_8, 0);
x_81 = lean_ctor_get(x_8, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_8);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("MetaEval", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runMetaEval", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = lean_infer_type(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l_Lean_Meta_getDecLevel(x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__1;
lean_inc(x_2);
x_18 = l_Lean_Name_str___override(x_2, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore(x_18, x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__2;
x_23 = l_Lean_Name_str___override(x_2, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_3);
x_25 = l_Lean_Expr_const___override(x_23, x_24);
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__13;
x_27 = lean_array_push(x_26, x_12);
x_28 = lean_array_push(x_27, x_20);
lean_inc(x_4);
x_29 = lean_array_push(x_28, x_4);
lean_inc(x_5);
x_30 = lean_array_push(x_29, x_5);
x_31 = lean_array_push(x_30, x_1);
x_32 = l_Lean_mkAppN(x_25, x_31);
x_33 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
x_34 = lean_array_push(x_33, x_4);
x_35 = lean_array_push(x_34, x_5);
x_36 = 0;
x_37 = 1;
x_38 = 1;
x_39 = l_Lean_Meta_mkLambdaFVars(x_35, x_32, x_36, x_37, x_38, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_40, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
return x_11;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("opts", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Options", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__3;
lean_inc(x_1);
x_11 = l_Lean_Name_str___override(x_1, x_10);
lean_inc(x_2);
x_12 = l_Lean_Expr_const___override(x_11, x_2);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1), 10, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_4);
x_14 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__2;
x_15 = 0;
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_14, x_15, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("env", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Environment", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_box(0);
x_8 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2), 9, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_1);
x_10 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__2;
x_11 = 0;
x_12 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__5;
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_10, x_11, x_12, x_9, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eval", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("runEval", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = l_Lean_Meta_getDecLevel(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore(x_13, x_1, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__4;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
x_21 = l_Lean_mkSimpleThunk(x_1);
x_22 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__5;
x_23 = lean_array_push(x_22, x_8);
x_24 = lean_array_push(x_23, x_15);
x_25 = lean_array_push(x_24, x_21);
x_26 = l_Lean_mkAppN(x_20, x_25);
x_27 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_26, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_compileDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___rarg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_dec(x_1);
lean_dec(x_12);
x_15 = l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_7, 5);
x_13 = lean_apply_1(x_2, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = 0;
x_21 = l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_1, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_io_error_to_string(x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_box(0);
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
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_io_error_to_string(x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_12);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_13, 0, x_39);
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_13, 0);
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_13);
x_42 = lean_io_error_to_string(x_40);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_12);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_isProp(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = l_Lean_Meta_mkDecide(x_1, x_5, x_6, x_7, x_8, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1;
x_2 = l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_90; lean_object* x_91; 
x_90 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_91 = l_Lean_Elab_Term_elabTerm(x_3, x_4, x_90, x_90, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_95 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_94, x_94, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_inc(x_92);
x_97 = l_Lean_Meta_getMVars(x_92, x_7, x_8, x_9, x_10, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_98, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
lean_dec(x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_105 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(x_92, x_104, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_12 = x_106;
x_13 = x_107;
goto block_89;
}
else
{
uint8_t x_108; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_105);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_dec(x_100);
x_113 = l_Lean_Elab_throwAbortTerm___at_Lean_Elab_Term_evalTerm___spec__1___rarg(x_112);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
return x_113;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_100);
if (x_118 == 0)
{
return x_100;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_100, 0);
x_120 = lean_ctor_get(x_100, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_100);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_95);
if (x_122 == 0)
{
return x_95;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_95, 0);
x_124 = lean_ctor_get(x_95, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_95);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_91);
if (x_126 == 0)
{
return x_91;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_91, 0);
x_128 = lean_ctor_get(x_91, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_91);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
block_89:
{
lean_object* x_14; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval(x_12, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_10, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1;
x_26 = l_Lean_Elab_Term_levelMVarToParam(x_22, x_24, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_30 = lean_infer_type(x_29, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2;
lean_inc(x_29);
x_35 = l_Lean_CollectLevelParams_main(x_29, x_34);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_to_list(lean_box(0), x_36);
lean_inc(x_2);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_31);
lean_inc(x_2);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_33);
x_43 = lean_box(0);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_46);
x_47 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_49 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_5);
x_51 = l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(x_1, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_49, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_dec(x_49);
x_66 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_46);
lean_dec(x_2);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
lean_dec(x_47);
x_73 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_29);
lean_dec(x_2);
x_78 = lean_ctor_get(x_30, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_30, 1);
lean_inc(x_79);
lean_dec(x_30);
x_80 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
lean_ctor_set_tag(x_80, 1);
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_14);
if (x_85 == 0)
{
return x_14;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_14, 0);
x_87 = lean_ctor_get(x_14, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_14);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed), 11, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
x_15 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_14, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_array_get_size(x_6);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_20 = l_Array_toSubarray___rarg(x_6, x_19, x_18);
x_21 = lean_ctor_get(x_1, 6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_array_get_size(x_21);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_21, x_24, x_25, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_7, 6);
lean_dec(x_31);
lean_ctor_set(x_7, 6, x_29);
x_32 = l_Lean_Core_resetMessageLog(x_11, x_12, x_28);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___boxed), 13, 4);
lean_closure_set(x_34, 0, x_2);
lean_closure_set(x_34, 1, x_3);
lean_closure_set(x_34, 2, x_4);
lean_closure_set(x_34, 3, x_5);
x_35 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_36 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_6, x_35, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
x_39 = lean_ctor_get(x_7, 2);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 1);
x_42 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 2);
x_43 = lean_ctor_get(x_7, 3);
x_44 = lean_ctor_get(x_7, 4);
x_45 = lean_ctor_get(x_7, 5);
x_46 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 3);
x_47 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 4);
x_48 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 5);
x_49 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 6);
x_50 = lean_ctor_get(x_7, 7);
x_51 = lean_ctor_get_uint8(x_7, sizeof(void*)*8 + 7);
lean_inc(x_50);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_52 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_38);
lean_ctor_set(x_52, 2, x_39);
lean_ctor_set(x_52, 3, x_43);
lean_ctor_set(x_52, 4, x_44);
lean_ctor_set(x_52, 5, x_45);
lean_ctor_set(x_52, 6, x_29);
lean_ctor_set(x_52, 7, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*8, x_40);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 1, x_41);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 2, x_42);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 3, x_46);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 4, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 5, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 6, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*8 + 7, x_51);
x_53 = l_Lean_Core_resetMessageLog(x_11, x_12, x_28);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___boxed), 13, 4);
lean_closure_set(x_55, 0, x_2);
lean_closure_set(x_55, 1, x_3);
lean_closure_set(x_55, 2, x_4);
lean_closure_set(x_55, 3, x_5);
x_56 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_57 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_6, x_56, x_55, x_52, x_8, x_9, x_10, x_11, x_12, x_54);
return x_57;
}
}
else
{
uint8_t x_58; 
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
x_58 = !lean_is_exclusive(x_15);
if (x_58 == 0)
{
return x_15;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_15, 0);
x_60 = lean_ctor_get(x_15, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_15);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_10, 5);
x_16 = lean_apply_3(x_5, x_1, x_2, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = 0;
x_24 = l_Lean_logAt___at_Lean_Elab_Term_traceAtCmdPos___spec__3(x_3, x_22, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_io_error_to_string(x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__5(x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
lean_dec(x_8);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_32, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_8);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_4);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_io_error_to_string(x_39);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_inc(x_15);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_16, 0, x_43);
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_io_error_to_string(x_44);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_inc(x_15);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = l_Lean_Expr_const___override(x_1, x_2);
x_14 = l_Lean_Expr_app___override(x_13, x_3);
x_15 = 1;
x_16 = l_Lean_Elab_Term_evalTerm___rarg(x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("CommandElabM", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Unit", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("term_>>=_", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(">>=", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fun", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("basicFun", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("v", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__11;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO.println", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__16;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__16;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__17;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IO", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("println", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__20;
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__22;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("repr", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__27;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__29;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__30;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_212; lean_object* x_213; 
x_212 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_213 = l_Lean_Elab_Term_elabTerm(x_6, x_3, x_212, x_212, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_217 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_216, x_216, x_7, x_8, x_9, x_10, x_11, x_12, x_215);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
lean_inc(x_214);
x_219 = l_Lean_Meta_getMVars(x_214, x_9, x_10, x_11, x_12, x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_222 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_220, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_221);
lean_dec(x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_unbox(x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_227 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(x_214, x_226, x_7, x_8, x_9, x_10, x_11, x_12, x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_14 = x_228;
x_15 = x_229;
goto block_211;
}
else
{
uint8_t x_230; 
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
x_230 = !lean_is_exclusive(x_227);
if (x_230 == 0)
{
return x_227;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_227, 0);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_227);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
lean_dec(x_214);
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
x_234 = lean_ctor_get(x_222, 1);
lean_inc(x_234);
lean_dec(x_222);
x_235 = l_Lean_Elab_throwAbortTerm___at_Lean_Elab_Term_evalTerm___spec__1___rarg(x_234);
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
return x_235;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_235, 0);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_235);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_214);
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
x_240 = !lean_is_exclusive(x_222);
if (x_240 == 0)
{
return x_222;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_222, 0);
x_242 = lean_ctor_get(x_222, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_222);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
else
{
uint8_t x_244; 
lean_dec(x_214);
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
x_244 = !lean_is_exclusive(x_217);
if (x_244 == 0)
{
return x_217;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_217, 0);
x_246 = lean_ctor_get(x_217, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_217);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
uint8_t x_248; 
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
x_248 = !lean_is_exclusive(x_213);
if (x_248 == 0)
{
return x_213;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_213, 0);
x_250 = lean_ctor_get(x_213, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_213);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
block_211:
{
lean_object* x_16; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_14);
x_16 = lean_infer_type(x_14, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__9;
x_23 = l_Lean_Name_str___override(x_1, x_22);
x_24 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5;
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__1;
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = l_Lean_Expr_isAppOfArity(x_20, x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval(x_14, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_12, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_11, 2);
lean_inc(x_37);
x_38 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1;
x_42 = l_Lean_Elab_Term_levelMVarToParam(x_39, x_28, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_45);
x_46 = lean_infer_type(x_45, x_9, x_10, x_11, x_12, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(0);
x_50 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2;
lean_inc(x_45);
x_51 = l_Lean_CollectLevelParams_main(x_45, x_50);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_to_list(lean_box(0), x_52);
lean_inc(x_4);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_47);
lean_inc(x_4);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_49);
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_61, 3, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*4, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_62);
x_63 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_62, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l_Lean_addAndCompile___at_Lean_Elab_Command_elabEvalUnsafe___spec__1(x_62, x_7, x_8, x_9, x_10, x_11, x_12, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_7);
x_67 = l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_36);
x_70 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(x_36, x_37, x_2, x_3, x_68, x_7, x_8, x_9, x_10, x_11, x_12, x_71);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_67, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_dec(x_67);
x_75 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_74);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_73);
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_65, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
lean_dec(x_65);
x_82 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_81);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
lean_ctor_set_tag(x_82, 1);
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_62);
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_ctor_get(x_63, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
lean_dec(x_63);
x_89 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_88);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set_tag(x_89, 1);
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_45);
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_46, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_46, 1);
lean_inc(x_95);
lean_dec(x_46);
x_96 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_30);
if (x_101 == 0)
{
return x_30;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_30, 0);
x_103 = lean_ctor_get(x_30, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_30);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_105 = l_Lean_Elab_Term_exprToSyntax(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_109 = lean_box(0);
x_110 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__4;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_111 = l_Lean_Meta_isExprDefEq(x_108, x_110, x_9, x_10, x_11, x_12, x_107);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
lean_inc(x_11);
x_115 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_11, x_12, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_11, 10);
lean_inc(x_118);
x_119 = lean_st_ref_get(x_12, x_117);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_environment_main_module(x_122);
x_124 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__7;
lean_inc(x_116);
x_125 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_124);
x_126 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__1;
x_127 = l_Lean_Name_str___override(x_5, x_126);
x_128 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__8;
lean_inc(x_127);
x_129 = l_Lean_Name_str___override(x_127, x_128);
lean_inc(x_116);
x_130 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_130, 0, x_116);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__9;
lean_inc(x_127);
x_132 = l_Lean_Name_str___override(x_127, x_131);
x_133 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__13;
lean_inc(x_118);
lean_inc(x_123);
x_134 = l_Lean_addMacroScope(x_123, x_133, x_118);
x_135 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__12;
lean_inc(x_116);
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_116);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_109);
x_137 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__5;
x_138 = lean_array_push(x_137, x_136);
x_139 = lean_box(2);
x_140 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
x_141 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_138);
x_142 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__14;
lean_inc(x_116);
x_143 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_143, 0, x_116);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__15;
lean_inc(x_127);
x_145 = l_Lean_Name_str___override(x_127, x_144);
x_146 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__22;
lean_inc(x_118);
lean_inc(x_123);
x_147 = l_Lean_addMacroScope(x_123, x_146, x_118);
x_148 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__18;
x_149 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__24;
lean_inc(x_116);
x_150 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_150, 0, x_116);
lean_ctor_set(x_150, 1, x_148);
lean_ctor_set(x_150, 2, x_147);
lean_ctor_set(x_150, 3, x_149);
x_151 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__25;
x_152 = l_Lean_Name_str___override(x_127, x_151);
x_153 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__10;
lean_inc(x_116);
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_116);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__29;
x_156 = l_Lean_addMacroScope(x_123, x_155, x_118);
x_157 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__28;
x_158 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__31;
lean_inc(x_116);
x_159 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_159, 0, x_116);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_159, 2, x_156);
lean_ctor_set(x_159, 3, x_158);
x_160 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
x_161 = lean_array_push(x_160, x_159);
lean_inc(x_141);
x_162 = lean_array_push(x_161, x_141);
lean_inc(x_145);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_139);
lean_ctor_set(x_163, 1, x_145);
lean_ctor_set(x_163, 2, x_162);
x_164 = lean_array_push(x_160, x_163);
x_165 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11;
x_166 = lean_array_push(x_164, x_165);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_139);
lean_ctor_set(x_167, 1, x_140);
lean_ctor_set(x_167, 2, x_166);
x_168 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__12;
x_169 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_169, 0, x_116);
lean_ctor_set(x_169, 1, x_168);
x_170 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__5;
x_171 = lean_array_push(x_170, x_154);
x_172 = lean_array_push(x_171, x_167);
x_173 = lean_array_push(x_172, x_169);
x_174 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_174, 0, x_139);
lean_ctor_set(x_174, 1, x_152);
lean_ctor_set(x_174, 2, x_173);
x_175 = lean_array_push(x_137, x_174);
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_139);
lean_ctor_set(x_176, 1, x_140);
lean_ctor_set(x_176, 2, x_175);
x_177 = lean_array_push(x_160, x_150);
x_178 = lean_array_push(x_177, x_176);
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_139);
lean_ctor_set(x_179, 1, x_145);
lean_ctor_set(x_179, 2, x_178);
x_180 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6;
x_181 = lean_array_push(x_180, x_141);
x_182 = lean_array_push(x_181, x_165);
x_183 = lean_array_push(x_182, x_143);
x_184 = lean_array_push(x_183, x_179);
x_185 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_185, 0, x_139);
lean_ctor_set(x_185, 1, x_132);
lean_ctor_set(x_185, 2, x_184);
x_186 = lean_array_push(x_160, x_130);
x_187 = lean_array_push(x_186, x_185);
x_188 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_188, 0, x_139);
lean_ctor_set(x_188, 1, x_129);
lean_ctor_set(x_188, 2, x_187);
x_189 = lean_array_push(x_170, x_106);
x_190 = lean_array_push(x_189, x_125);
x_191 = lean_array_push(x_190, x_188);
x_192 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__6;
x_193 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_193, 0, x_139);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_191);
x_194 = lean_box(0);
x_195 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(x_27, x_109, x_110, x_193, x_194, x_7, x_8, x_9, x_10, x_11, x_12, x_121);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_5);
x_196 = lean_ctor_get(x_111, 1);
lean_inc(x_196);
lean_dec(x_111);
x_197 = lean_box(0);
x_198 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(x_27, x_109, x_110, x_106, x_197, x_7, x_8, x_9, x_10, x_11, x_12, x_196);
return x_198;
}
}
else
{
uint8_t x_199; 
lean_dec(x_106);
lean_dec(x_27);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_199 = !lean_is_exclusive(x_111);
if (x_199 == 0)
{
return x_111;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_111, 0);
x_201 = lean_ctor_get(x_111, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_111);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_203 = !lean_is_exclusive(x_105);
if (x_203 == 0)
{
return x_105;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_105, 0);
x_205 = lean_ctor_get(x_105, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_105);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_14);
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
x_207 = !lean_is_exclusive(x_16);
if (x_207 == 0)
{
return x_16;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_16, 0);
x_209 = lean_ctor_get(x_16, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_16);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8), 13, 6);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
x_17 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_16, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_array_get_size(x_8);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
x_22 = l_Array_toSubarray___rarg(x_8, x_21, x_20);
x_23 = lean_ctor_get(x_1, 6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_array_get_size(x_23);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_23, x_26, x_27, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_9, 6);
lean_dec(x_33);
lean_ctor_set(x_9, 6, x_31);
x_34 = l_Lean_Core_resetMessageLog(x_13, x_14, x_30);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__9___boxed), 15, 6);
lean_closure_set(x_36, 0, x_2);
lean_closure_set(x_36, 1, x_3);
lean_closure_set(x_36, 2, x_4);
lean_closure_set(x_36, 3, x_5);
lean_closure_set(x_36, 4, x_6);
lean_closure_set(x_36, 5, x_7);
x_37 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_38 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_8, x_37, x_36, x_9, x_10, x_11, x_12, x_13, x_14, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
x_43 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 1);
x_44 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 2);
x_45 = lean_ctor_get(x_9, 3);
x_46 = lean_ctor_get(x_9, 4);
x_47 = lean_ctor_get(x_9, 5);
x_48 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 3);
x_49 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 4);
x_50 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 5);
x_51 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 6);
x_52 = lean_ctor_get(x_9, 7);
x_53 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 7);
lean_inc(x_52);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_54 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_54, 0, x_39);
lean_ctor_set(x_54, 1, x_40);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set(x_54, 4, x_46);
lean_ctor_set(x_54, 5, x_47);
lean_ctor_set(x_54, 6, x_31);
lean_ctor_set(x_54, 7, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*8, x_42);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 1, x_43);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 2, x_44);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 3, x_48);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 4, x_49);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 5, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 6, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*8 + 7, x_53);
x_55 = l_Lean_Core_resetMessageLog(x_13, x_14, x_30);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__9___boxed), 15, 6);
lean_closure_set(x_57, 0, x_2);
lean_closure_set(x_57, 1, x_3);
lean_closure_set(x_57, 2, x_4);
lean_closure_set(x_57, 3, x_5);
lean_closure_set(x_57, 4, x_6);
lean_closure_set(x_57, 5, x_7);
x_58 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_59 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_8, x_58, x_57, x_54, x_10, x_11, x_12, x_13, x_14, x_56);
return x_59;
}
}
else
{
uint8_t x_60; 
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
x_60 = !lean_is_exclusive(x_17);
if (x_60 == 0)
{
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eval", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_eval", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabEvalUnsafe___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_2 = l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_st_ref_get(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_elabEvalUnsafe___closed__6;
x_18 = l_Lean_Environment_contains(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = l_Lean_Elab_Command_getScope___rarg(x_3, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 5);
lean_inc(x_22);
x_23 = l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___boxed), 13, 5);
lean_closure_set(x_24, 0, x_20);
lean_closure_set(x_24, 1, x_9);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_11);
lean_closure_set(x_24, 4, x_12);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_Lean_Elab_Command_elabEvalUnsafe___closed__5;
x_28 = l_Lean_Elab_Command_liftTermElabM___rarg(x_27, x_26, x_2, x_3, x_21);
lean_dec(x_3);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = l_Lean_Elab_Command_getScope___rarg(x_3, x_15);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 5);
lean_inc(x_32);
x_33 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2;
x_34 = l_Lean_Elab_Command_elabEvalUnsafe___closed__4;
x_35 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4;
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe___lambda__10___boxed), 15, 7);
lean_closure_set(x_36, 0, x_30);
lean_closure_set(x_36, 1, x_33);
lean_closure_set(x_36, 2, x_9);
lean_closure_set(x_36, 3, x_12);
lean_closure_set(x_36, 4, x_34);
lean_closure_set(x_36, 5, x_35);
lean_closure_set(x_36, 6, x_11);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_37, 0, x_32);
lean_closure_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = l_Lean_Elab_Command_elabEvalUnsafe___closed__5;
lean_inc(x_2);
x_40 = l_Lean_Elab_Command_liftTermElabM___rarg(x_39, x_38, x_2, x_3, x_31);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_apply_3(x_49, x_2, x_3, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 0);
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_ofExcept___at_Lean_Elab_Command_elabEvalUnsafe___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConst___at_Lean_Elab_Command_elabEvalUnsafe___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabEvalUnsafe___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabEvalUnsafe___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_elabEvalUnsafe___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_16;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabEval", 8);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabEvalUnsafe), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEval(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabEvalUnsafe___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(377u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(377u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__2;
x_4 = lean_unsigned_to_nat(29u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(377u);
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(377u);
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__4;
x_2 = lean_unsigned_to_nat(7u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__5;
x_4 = lean_unsigned_to_nat(15u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabEval_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabEval___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_2);
x_11 = l_Lean_Elab_Term_elabTerm(x_1, x_2, x_10, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_14, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_synthInstance(x_18, x_2, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = 0;
x_25 = l_Lean_log___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_23, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__1), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Elab_Term_withoutAutoBoundImplicit___rarg(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Elab_Term_synthesizeSyntheticMVars(x_11, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_array_get_size(x_3);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_17 = l_Array_toSubarray___rarg(x_3, x_16, x_15);
x_18 = lean_ctor_get(x_1, 6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_array_get_size(x_18);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_runTermElabM___spec__1(x_18, x_21, x_22, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_4, 6);
lean_dec(x_28);
lean_ctor_set(x_4, 6, x_26);
x_29 = l_Lean_Core_resetMessageLog(x_8, x_9, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__2___boxed), 10, 1);
lean_closure_set(x_31, 0, x_2);
x_32 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_33 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_3, x_32, x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
x_36 = lean_ctor_get(x_4, 2);
x_37 = lean_ctor_get_uint8(x_4, sizeof(void*)*8);
x_38 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 1);
x_39 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 2);
x_40 = lean_ctor_get(x_4, 3);
x_41 = lean_ctor_get(x_4, 4);
x_42 = lean_ctor_get(x_4, 5);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 3);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 4);
x_45 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 5);
x_46 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 6);
x_47 = lean_ctor_get(x_4, 7);
x_48 = lean_ctor_get_uint8(x_4, sizeof(void*)*8 + 7);
lean_inc(x_47);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_49 = lean_alloc_ctor(0, 8, 8);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_35);
lean_ctor_set(x_49, 2, x_36);
lean_ctor_set(x_49, 3, x_40);
lean_ctor_set(x_49, 4, x_41);
lean_ctor_set(x_49, 5, x_42);
lean_ctor_set(x_49, 6, x_26);
lean_ctor_set(x_49, 7, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*8, x_37);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 1, x_38);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 2, x_39);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 3, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 4, x_44);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 5, x_45);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 6, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*8 + 7, x_48);
x_50 = l_Lean_Core_resetMessageLog(x_8, x_9, x_25);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__2___boxed), 10, 1);
lean_closure_set(x_52, 0, x_2);
x_53 = l_Lean_Elab_Command_elabVariable___lambda__3___closed__1;
x_54 = l_Lean_Elab_Term_addAutoBoundImplicits_x27___rarg(x_3, x_53, x_52, x_49, x_5, x_6, x_7, x_8, x_9, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_synth_cmd", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabSynth___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabSynth___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_getScope___rarg(x_3, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 5);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___lambda__3___boxed), 10, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_6);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withAutoBoundImplicit___rarg), 8, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Command_elabSynth___closed__3;
lean_inc(x_2);
x_19 = l_Lean_Elab_Command_liftTermElabM___rarg(x_18, x_17, x_2, x_3, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_21);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_setEnv___at_Lean_Elab_Command_elabInitQuot___spec__1(x_10, x_2, x_3, x_28);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabSynth___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabSynth___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSynth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSynth(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("synth", 5);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSynth", 9);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSynth___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(379u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(387u);
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__1;
x_2 = lean_unsigned_to_nat(30u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__2;
x_4 = lean_unsigned_to_nat(11u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(379u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(379u);
x_2 = lean_unsigned_to_nat(43u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__4;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__5;
x_4 = lean_unsigned_to_nat(43u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSynth_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSynth___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSetOption___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Command_instInhabitedScope;
x_12 = l_List_head_x21___rarg(x_11, x_10);
lean_dec(x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_KVMap_insertCore(x_13, x_1, x_2);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Command_instInhabitedScope;
x_19 = l_List_head_x21___rarg(x_18, x_17);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_KVMap_insertCore(x_20, x_1, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("type mismatch at set_option", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lean_getOptionDecl(x_1, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_DataValue_sameCtor(x_12, x_2);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__2;
x_15 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_14, x_3, x_4, x_11);
lean_dec(x_4);
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
x_21 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___lambda__1(x_1, x_2, x_20, x_3, x_4, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_io_error_to_string(x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_9, 0, x_27);
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_io_error_to_string(x_28);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected set_option value ", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Syntax_getArgs(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Array_toSubarray___rarg(x_9, x_10, x_11);
x_13 = l_Array_ofSubarray___rarg(x_12);
x_14 = l_Lean_Syntax_setArgs(x_7, x_13);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_addCompletionInfo___at_Lean_Elab_Command_elabEnd___spec__2(x_15, x_3, x_4, x_8);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_19 = lean_erase_macro_scopes(x_18);
x_20 = l_Lean_Syntax_isStrLit_x3f(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Syntax_isNatLit_x3f(x_2);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__3;
x_24 = lean_string_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__4;
x_26 = lean_string_dec_eq(x_22, x_25);
lean_dec(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_2);
x_28 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Elab_Command_elabSetOption___spec__2(x_31, x_3, x_4, x_17);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_33 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__5;
x_34 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3(x_19, x_33, x_3, x_4, x_17);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
lean_dec(x_2);
x_35 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__6;
x_36 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3(x_19, x_35, x_3, x_4, x_17);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_2);
x_38 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Command_elabSetOption___spec__2(x_41, x_3, x_4, x_17);
lean_dec(x_4);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3(x_19, x_44, x_3, x_4, x_17);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
lean_dec(x_20);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3(x_19, x_47, x_3, x_4, x_17);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSetOption___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
x_9 = lean_ctor_get(x_2, 5);
x_10 = lean_ctor_get(x_2, 6);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_8);
lean_ctor_set(x_12, 5, x_9);
lean_ctor_set(x_12, 6, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*7, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1(x_6, x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_13, 4);
lean_dec(x_16);
x_17 = l_Lean_Elab_Command_elabSetOption___closed__1;
x_18 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_10, x_17);
lean_ctor_set(x_13, 4, x_18);
x_19 = lean_st_ref_set(x_3, x_13, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption___lambda__1), 2, 1);
lean_closure_set(x_21, 0, x_10);
x_22 = l_Lean_Elab_Command_modifyScope(x_21, x_2, x_3, x_20);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_ctor_get(x_13, 2);
x_26 = lean_ctor_get(x_13, 3);
x_27 = lean_ctor_get(x_13, 5);
x_28 = lean_ctor_get(x_13, 6);
x_29 = lean_ctor_get(x_13, 7);
x_30 = lean_ctor_get(x_13, 8);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_31 = l_Lean_Elab_Command_elabSetOption___closed__1;
x_32 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_10, x_31);
x_33 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_27);
lean_ctor_set(x_33, 6, x_28);
lean_ctor_set(x_33, 7, x_29);
lean_ctor_set(x_33, 8, x_30);
x_34 = lean_st_ref_set(x_3, x_33, x_14);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption___lambda__1), 2, 1);
lean_closure_set(x_36, 0, x_10);
x_37 = l_Lean_Elab_Command_modifyScope(x_36, x_2, x_3, x_35);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabSetOption___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabSetOption___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabSetOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabSetOption(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("set_option", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabSetOption", 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabSetOption___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(389u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(392u);
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__1;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__2;
x_4 = lean_unsigned_to_nat(57u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(389u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(389u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__4;
x_2 = lean_unsigned_to_nat(39u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__5;
x_4 = lean_unsigned_to_nat(52u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("in", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandInCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_expandInCmd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandInCmd(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_expandInCmd___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_3);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Elab_Command_elabSection___closed__1;
lean_inc(x_14);
x_16 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11;
x_20 = lean_array_push(x_18, x_19);
x_21 = lean_box(2);
x_22 = l_Lean_Elab_Command_elabSection___closed__2;
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
x_24 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_17, x_25);
x_27 = lean_array_push(x_26, x_19);
x_28 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_27);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6;
x_31 = lean_array_push(x_30, x_23);
x_32 = lean_array_push(x_31, x_9);
x_33 = lean_array_push(x_32, x_11);
x_34 = lean_array_push(x_33, x_29);
x_35 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_12, 0, x_36);
return x_12;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_37 = lean_ctor_get(x_12, 0);
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_12);
x_39 = l_Lean_Elab_Command_elabSection___closed__1;
lean_inc(x_37);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9;
x_42 = lean_array_push(x_41, x_40);
x_43 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11;
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_box(2);
x_46 = l_Lean_Elab_Command_elabSection___closed__2;
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_44);
x_48 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1;
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_push(x_41, x_49);
x_51 = lean_array_push(x_50, x_43);
x_52 = l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2;
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_51);
x_54 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6;
x_55 = lean_array_push(x_54, x_47);
x_56 = lean_array_push(x_55, x_9);
x_57 = lean_array_push(x_56, x_11);
x_58 = lean_array_push(x_57, x_53);
x_59 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4;
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_38);
return x_61;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expandInCmd", 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandInCmd), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3;
x_3 = l_Lean_Elab_Command_expandInCmd___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(394u);
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(396u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__1;
x_2 = lean_unsigned_to_nat(41u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__2;
x_4 = lean_unsigned_to_nat(47u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(394u);
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(394u);
x_2 = lean_unsigned_to_nat(56u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__4;
x_2 = lean_unsigned_to_nat(45u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__5;
x_4 = lean_unsigned_to_nat(56u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__12(x_2, x_20, x_4, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabAddDeclDoc___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Command_getScope___rarg(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getScope___rarg(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_ResolveName_resolveGlobalName(x_8, x_12, x_16, x_1);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_ResolveName_resolveGlobalName(x_8, x_12, x_20, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAddDeclDoc___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_1, x_5);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__3;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_expandDeclId___spec__4(x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabAddDeclDoc___spec__5(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_filterTRAux___at_Lean_resolveGlobalConstCore___spec__1(x_6, x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4___lambda__1(x_9, x_8, x_11, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_9);
x_13 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAddDeclDoc___spec__6(x_1, x_2, x_3, x_7);
lean_dec(x_3);
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
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(x_6);
x_8 = l_List_isEmpty___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_2, 6);
lean_dec(x_15);
lean_ctor_set(x_2, 6, x_13);
x_16 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4(x_5, x_2, x_3, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_ctor_get(x_2, 7);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_24, 5, x_22);
lean_ctor_set(x_24, 6, x_13);
lean_ctor_set(x_24, 7, x_23);
x_25 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4(x_5, x_24, x_3, x_12);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__3;
x_27 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__3(x_1, x_26, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__8(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__8(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabAddDeclDoc___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = l_Lean_Syntax_formatStxAux(x_8, x_9, x_10, x_1);
x_12 = l_Std_Format_defWidth;
x_13 = lean_format_pretty(x_11, x_12);
x_14 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_6, x_18);
x_20 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_19);
x_21 = lean_string_append(x_17, x_20);
lean_dec(x_20);
x_22 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__7(x_1, x_25, x_2, x_3, x_7);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_30);
return x_5;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_27);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_dec(x_5);
x_35 = lean_box(0);
x_36 = 0;
x_37 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_38 = l_Lean_Syntax_formatStxAux(x_35, x_36, x_37, x_1);
x_39 = l_Std_Format_defWidth;
x_40 = lean_format_pretty(x_38, x_39);
x_41 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_box(0);
x_46 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_6, x_45);
x_47 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_46);
x_48 = lean_string_append(x_44, x_47);
lean_dec(x_47);
x_49 = l_Lean_Elab_Command_elabModuleDoc___closed__3;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__7(x_1, x_52, x_2, x_3, x_34);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_5);
if (x_54 == 0)
{
return x_5;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_5, 0);
x_56 = lean_ctor_get(x_5, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_5);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Elab_getBetterRef(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_instAddMessageContextCommandElabM___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_instAddErrorMessageContextCommandElabM___spec__1(x_11, x_8, x_2, x_3, x_12);
lean_dec(x_2);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_Command_getRef(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 6);
lean_dec(x_11);
lean_ctor_set(x_3, 6, x_9);
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__11(x_2, x_3, x_4, x_8);
lean_dec(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
x_19 = lean_ctor_get(x_3, 7);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_17);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__11(x_2, x_20, x_4, x_8);
lean_dec(x_4);
return x_21;
}
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected doc string", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_utf8_byte_size(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_extract(x_7, x_11, x_10);
lean_dec(x_10);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_6);
x_15 = l_Lean_indentD(x_14);
x_16 = l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Command_elabModuleDoc___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__10(x_1, x_19, x_2, x_3, x_4);
return x_20;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("addDocString", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabAddDeclDoc___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docComment", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6;
x_2 = l_Lean_Elab_Command_elabAddDeclDoc___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabAddDeclDoc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabAddDeclDoc___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Elab_Command_elabAddDeclDoc___closed__4;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg(x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_resolveGlobalConstNoOverload___at_Lean_Elab_Command_elabAddDeclDoc___spec__1(x_14, x_2, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9(x_9, x_2, x_3, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_addDocString___at_Lean_Elab_Command_expandDeclId___spec__10(x_16, x_19, x_2, x_3, x_20);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabAddDeclDoc___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabAddDeclDoc___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveGlobalName___at_Lean_Elab_Command_elabAddDeclDoc___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAddDeclDoc___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabAddDeclDoc___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConstCore___at_Lean_Elab_Command_elabAddDeclDoc___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabAddDeclDoc___spec__11(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabAddDeclDoc", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11;
x_2 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAddDeclDoc), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14;
x_3 = l_Lean_Elab_Command_elabAddDeclDoc___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(398u);
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(403u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__1;
x_2 = lean_unsigned_to_nat(50u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(398u);
x_2 = lean_unsigned_to_nat(54u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(398u);
x_2 = lean_unsigned_to_nat(68u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__4;
x_2 = lean_unsigned_to_nat(54u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__5;
x_4 = lean_unsigned_to_nat(68u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Eval(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Open(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinCommand(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Eval(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Open(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabModuleDoc___closed__1 = _init_l_Lean_Elab_Command_elabModuleDoc___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabModuleDoc___closed__1);
l_Lean_Elab_Command_elabModuleDoc___closed__2 = _init_l_Lean_Elab_Command_elabModuleDoc___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabModuleDoc___closed__2);
l_Lean_Elab_Command_elabModuleDoc___closed__3 = _init_l_Lean_Elab_Command_elabModuleDoc___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabModuleDoc___closed__3);
l_Lean_Elab_Command_elabModuleDoc___closed__4 = _init_l_Lean_Elab_Command_elabModuleDoc___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabModuleDoc___closed__4);
l_Lean_Elab_Command_elabModuleDoc___closed__5 = _init_l_Lean_Elab_Command_elabModuleDoc___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabModuleDoc___closed__5);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__1);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__2);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__3);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__4);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__5);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__6);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__7);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__8 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__8);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__9 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__9);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__10 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__10);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__11);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__12 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__12();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__12);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__13 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__13();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__13);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__14);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__15 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__15();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc___closed__15);
res = l___regBuiltin_Lean_Elab_Command_elabModuleDoc(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabModuleDoc_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1 = _init_l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1();
lean_mark_persistent(l_Lean_pushScope___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScope___spec__1___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_addScopes___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabNamespace___spec__1___rarg___closed__2);
l_Lean_Elab_Command_elabNamespace___closed__1 = _init_l_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabNamespace___closed__1);
l_Lean_Elab_Command_elabNamespace___closed__2 = _init_l_Lean_Elab_Command_elabNamespace___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabNamespace___closed__2);
l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__1);
l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__2);
l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabNamespace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabNamespace_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSection___closed__1 = _init_l_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSection___closed__1);
l_Lean_Elab_Command_elabSection___closed__2 = _init_l_Lean_Elab_Command_elabSection___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSection___closed__2);
l_Lean_Elab_Command_elabSection___closed__3 = _init_l_Lean_Elab_Command_elabSection___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSection___closed__3);
l_Lean_Elab_Command_elabSection___closed__4 = _init_l_Lean_Elab_Command_elabSection___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabSection___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSection___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSection___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSection___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSection___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabSection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSection_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabSection_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabNonComputableSection___closed__1 = _init_l_Lean_Elab_Command_elabNonComputableSection___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabNonComputableSection___closed__1);
l_Lean_Elab_Command_elabNonComputableSection___closed__2 = _init_l_Lean_Elab_Command_elabNonComputableSection___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabNonComputableSection___closed__2);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__1);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__2);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabNonComputableSection_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__1 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__1);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__2 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__2);
l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3 = _init_l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3();
lean_mark_persistent(l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Command_elabEnd___spec__3___closed__3);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__1);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__2);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__3);
l_Lean_Elab_Command_elabEnd___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabEnd___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___lambda__1___closed__4);
l_Lean_Elab_Command_elabEnd___closed__1 = _init_l_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__1);
l_Lean_Elab_Command_elabEnd___closed__2 = _init_l_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEnd___closed__2);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__1);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__2);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__3);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__4);
l___regBuiltin_Lean_Elab_Command_elabEnd___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabEnd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEnd_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabEnd_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice___closed__1);
l___regBuiltin_Lean_Elab_Command_elabChoice___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice___closed__2);
l___regBuiltin_Lean_Elab_Command_elabChoice___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice___closed__3);
l___regBuiltin_Lean_Elab_Command_elabChoice___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice___closed__4);
l___regBuiltin_Lean_Elab_Command_elabChoice___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabChoice_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabChoice_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__1);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__2);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__3);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__4);
l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabUniverse(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabUniverse_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__1);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__2);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__3);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__4);
l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabInitQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabInitQuot_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1 = _init_l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1();
lean_mark_persistent(l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__1);
l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2 = _init_l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2();
lean_mark_persistent(l_Lean_resolveNamespace___at_Lean_Elab_Command_elabExport___spec__1___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__1 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__1);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__2 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__2);
l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__3 = _init_l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at_Lean_Elab_Command_elabExport___spec__8___closed__3);
l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1 = _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__1);
l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2 = _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_Elab_Command_elabExport___spec__5___closed__2);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__1);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__2 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__2();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__2);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__3 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__3();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__3);
l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__4 = _init_l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__4();
lean_mark_persistent(l_Lean_Elab_nestedExceptionToMessageData___at_Lean_Elab_Command_elabExport___spec__15___closed__4);
l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__1 = _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__1();
lean_mark_persistent(l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__1);
l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__2 = _init_l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__2();
lean_mark_persistent(l_Lean_Elab_throwErrorWithNestedErrors___at_Lean_Elab_Command_elabExport___spec__14___closed__2);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__1 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__1);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__2 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__2);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__3 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__3);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__4 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__4);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__5 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__5);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___lambda__1___closed__6);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__1);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__2 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__2);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__3 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__3);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__4 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__4);
l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__5 = _init_l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Open_0__Lean_Elab_OpenDecl_resolveNameUsingNamespacesCore___at_Lean_Elab_Command_elabExport___spec__3___closed__5);
l_Lean_Elab_Command_elabExport___closed__1 = _init_l_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__1);
l_Lean_Elab_Command_elabExport___closed__2 = _init_l_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExport___closed__2);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__1);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__2);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__3);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__4);
l___regBuiltin_Lean_Elab_Command_elabExport___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabExport___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabExport(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabExport_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabExport_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__1 = _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__1();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__1);
l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__2 = _init_l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__2();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___at_Lean_Elab_Command_elabOpen___spec__3___closed__2);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__1 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__1);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__2 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__2);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__3 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__3);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__4 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__4);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__5 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__5();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__5);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__6 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__6();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__6);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__7 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__7();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__7);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__8 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__8();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__8);
l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__9 = _init_l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__9();
lean_mark_persistent(l_Lean_Elab_OpenDecl_elabOpenDecl___at_Lean_Elab_Command_elabOpen___spec__1___closed__9);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__1);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__2);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__3);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__4);
l___regBuiltin_Lean_Elab_Command_elabOpen___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabOpen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabOpen_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabOpen_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__2);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__3 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__3);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__4);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__5 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__5);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__6 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_typelessBinder_x3f___closed__6);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_matchBinderNames___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__6);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__7 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__7);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__8 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__8);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__9);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__10 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__10);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__11);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__12 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__12);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__13 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__13();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___lambda__2___closed__13);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___spec__2___closed__5);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_replaceBinderAnnotation___closed__1);
l_Lean_Elab_Command_elabVariable___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabVariable___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabVariable___lambda__2___closed__1);
l_Lean_Elab_Command_elabVariable___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabVariable___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabVariable___lambda__3___closed__1);
l_Lean_Elab_Command_elabVariable___closed__1 = _init_l_Lean_Elab_Command_elabVariable___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabVariable___closed__1);
l_Lean_Elab_Command_elabVariable___closed__2 = _init_l_Lean_Elab_Command_elabVariable___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabVariable___closed__2);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__1);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__2);
l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabVariable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabVariable_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabVariable_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1 = _init_l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__1);
l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__2 = _init_l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__2);
l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__3 = _init_l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___lambda__2___closed__3);
l_Lean_Elab_Command_elabCheckCore___closed__1 = _init_l_Lean_Elab_Command_elabCheckCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___closed__1);
l_Lean_Elab_Command_elabCheckCore___closed__2 = _init_l_Lean_Elab_Command_elabCheckCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___closed__2);
l_Lean_Elab_Command_elabCheckCore___closed__3 = _init_l_Lean_Elab_Command_elabCheckCore___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___closed__3);
l_Lean_Elab_Command_elabCheckCore___closed__4 = _init_l_Lean_Elab_Command_elabCheckCore___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___closed__4);
l_Lean_Elab_Command_elabCheckCore___closed__5 = _init_l_Lean_Elab_Command_elabCheckCore___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckCore___closed__5);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__1);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__2);
l___regBuiltin_Lean_Elab_Command_elabCheck___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabCheck(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheck_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabCheck_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabReduce___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabReduce___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabReduce___lambda__1___closed__1);
l_Lean_Elab_Command_elabReduce___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabReduce___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabReduce___lambda__1___closed__2);
l_Lean_Elab_Command_elabReduce___closed__1 = _init_l_Lean_Elab_Command_elabReduce___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabReduce___closed__1);
l_Lean_Elab_Command_elabReduce___closed__2 = _init_l_Lean_Elab_Command_elabReduce___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabReduce___closed__2);
l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce___closed__1);
l___regBuiltin_Lean_Elab_Command_elabReduce___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce___closed__2);
l___regBuiltin_Lean_Elab_Command_elabReduce___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabReduce(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabReduce_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabReduce_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__1);
l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2 = _init_l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___lambda__1___closed__2);
l_Lean_Elab_Command_failIfSucceeds___closed__1 = _init_l_Lean_Elab_Command_failIfSucceeds___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_failIfSucceeds___closed__1);
l_Lean_Elab_Command_elabCheckFailure___closed__1 = _init_l_Lean_Elab_Command_elabCheckFailure___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckFailure___closed__1);
l_Lean_Elab_Command_elabCheckFailure___closed__2 = _init_l_Lean_Elab_Command_elabCheckFailure___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckFailure___closed__2);
l_Lean_Elab_Command_elabCheckFailure___closed__3 = _init_l_Lean_Elab_Command_elabCheckFailure___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabCheckFailure___closed__3);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__1);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__2);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabCheckFailure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabCheckFailure_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__2);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__3 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__3);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__4 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__4);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__5 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__5);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__6 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__6();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__6);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__7 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__7();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__7);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__8 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__8();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__8);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__9 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__9();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__9);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__10 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__10();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkEvalInstCore___closed__10);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__1___closed__2);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__2);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__3 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___lambda__2___closed__3);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__2);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__3 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__3);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__4 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__4);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__5 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunMetaEval___closed__5);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__1 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__1();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__1);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__2 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__2();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__2);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__3 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__3();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__3);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__4 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__4();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__4);
l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__5 = _init_l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__5();
lean_mark_persistent(l___private_Lean_Elab_BuiltinCommand_0__Lean_Elab_Command_mkRunEval___closed__5);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__3___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__4 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__4);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__5 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__5);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__6 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__6);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__7 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__7);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__8 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__8);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__9 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__9);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__10);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__11 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__11);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__12 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__12);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__13 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__13);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__14 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__14);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__15 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__15);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__16 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__16);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__17 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__17);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__18 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__18);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__19 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__19);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__20 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__20);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__21 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__21);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__22 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__22);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__23 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__23);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__24 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__24();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__24);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__25 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__25);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__26);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__27 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__27();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__27);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__28 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__28();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__28);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__29 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__29();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__29);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__30 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__30();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__30);
l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__31 = _init_l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__31();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___lambda__8___closed__31);
l_Lean_Elab_Command_elabEvalUnsafe___closed__1 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__1);
l_Lean_Elab_Command_elabEvalUnsafe___closed__2 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__2);
l_Lean_Elab_Command_elabEvalUnsafe___closed__3 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__3);
l_Lean_Elab_Command_elabEvalUnsafe___closed__4 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__4);
l_Lean_Elab_Command_elabEvalUnsafe___closed__5 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__5);
l_Lean_Elab_Command_elabEvalUnsafe___closed__6 = _init_l_Lean_Elab_Command_elabEvalUnsafe___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabEvalUnsafe___closed__6);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__1);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__2);
l___regBuiltin_Lean_Elab_Command_elabEval___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabEval___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabEval(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabEval_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabEval_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabSynth___closed__1 = _init_l_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__1);
l_Lean_Elab_Command_elabSynth___closed__2 = _init_l_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__2);
l_Lean_Elab_Command_elabSynth___closed__3 = _init_l_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabSynth___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSynth___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabSynth(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSynth_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabSynth_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__1 = _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__1);
l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__2 = _init_l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___at_Lean_Elab_Command_elabSetOption___spec__3___closed__2);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__1 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__1);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__2 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__2);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__3 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__3);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__4 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__4);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__5 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__5();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__5);
l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__6 = _init_l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__6();
lean_mark_persistent(l_Lean_Elab_elabSetOption___at_Lean_Elab_Command_elabSetOption___spec__1___closed__6);
l_Lean_Elab_Command_elabSetOption___closed__1 = _init_l_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabSetOption___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption___closed__5);
res = l___regBuiltin_Lean_Elab_Command_elabSetOption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabSetOption_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandInCmd___closed__1 = _init_l_Lean_Elab_Command_expandInCmd___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__1);
l_Lean_Elab_Command_expandInCmd___closed__2 = _init_l_Lean_Elab_Command_expandInCmd___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandInCmd___closed__2);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__1);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__2);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__3);
l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd___closed__4);
res = l___regBuiltin_Lean_Elab_Command_expandInCmd(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_expandInCmd_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__1 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__1);
l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__2 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__2);
l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__3 = _init_l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at_Lean_Elab_Command_elabAddDeclDoc___spec__2___closed__3);
l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__1 = _init_l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__1();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__1);
l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__2 = _init_l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__2();
lean_mark_persistent(l_Lean_getDocStringText___at_Lean_Elab_Command_elabAddDeclDoc___spec__9___closed__2);
l_Lean_Elab_Command_elabAddDeclDoc___closed__1 = _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAddDeclDoc___closed__1);
l_Lean_Elab_Command_elabAddDeclDoc___closed__2 = _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabAddDeclDoc___closed__2);
l_Lean_Elab_Command_elabAddDeclDoc___closed__3 = _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabAddDeclDoc___closed__3);
l_Lean_Elab_Command_elabAddDeclDoc___closed__4 = _init_l_Lean_Elab_Command_elabAddDeclDoc___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabAddDeclDoc___closed__4);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__2);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc___closed__3);
res = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabAddDeclDoc_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
