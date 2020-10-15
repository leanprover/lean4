// Lean compiler output
// Module: Lean.Elab.MutualDef
// Imports: Init Lean.Meta.Closure Lean.Meta.Check Lean.Elab.Command Lean.Elab.DefView Lean.Elab.PreDefinition
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
lean_object* l_Lean_Elab_Term_getLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType_match__1(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabBinders___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__3;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getAllUserLevelNames(lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_FixPoint_run_match__1(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLetRecsToLift___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_addInstanceEntry___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_Meta_findLocalDecl_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutualDef(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__1;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_MutualClosure_getKindForLetRecs(lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__2;
lean_object* l_Lean_Elab_Term_MutualClosure_ClosureState_exprArgs___default;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__4;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__3___rarg(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_elabMutualDef___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Elab_Term_MutualClosure_FixPoint_State_modified___default;
uint8_t l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__2(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__3;
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__2;
lean_object* lean_private_to_user_name(lean_object*);
lean_object* l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__1;
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen(lean_object*);
lean_object* l_ReaderT_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutualDef___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__4;
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getKindForLetRecs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_beq___main___at_Lean_OpenDecl_HasToString___spec__1(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__3(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_ClosureState_newLocalDecls___default;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified___rarg(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___at_Lean_LocalContext_erase___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Command_elabMutualDef___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__1;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__3(lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isExample(uint8_t);
lean_object* l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__1;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getMVarsImp___closed__1;
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___boxed(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap___rarg(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__2;
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutualDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__1;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__4;
lean_object* l_Lean_Meta_findLocalDecl_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_levelMVarToParamPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkLambda(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_mkDeclName___rarg___closed__2;
extern lean_object* l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___at_Lean_Elab_Command_elabMutualDef___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerCustomErrorIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_pushLetRecs(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_elabMutualDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Command_elabMutualDef___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_MutualClosure_pushLetRecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__1;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_FixPoint_run_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__6;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__2___rarg(lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply___boxed(lean_object*, lean_object*);
lean_object* l_Array_getMax_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__3;
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__2;
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_protectedExt;
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint_match__1(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check_match__1(lean_object*);
lean_object* l_Lean_CollectFVars_main___main(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__4(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getAllUserLevelNames___boxed(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor_match__1(lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__3;
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_MutualClosure_FixPoint_State_usedFVarsMap___default;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__3___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Elab_Term_MutualClosure_pushMain___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap_match__1(lean_object*);
lean_object* l_Lean_replaceFVarIdAtLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Array_getMax_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_Elab_expandDeclIdCore(lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_pushMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_feraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashSet_Inhabited___closed__1;
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars___spec__1(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen_match__1(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
extern lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3;
lean_object* l_Lean_Elab_Term_MutualClosure_ClosureState_localDecls___default;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap(lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addPreDefinitions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
lean_object* l_Lean_Elab_DefViewElabHeader_inhabited___closed__1;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__1(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__1;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__2;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes_match__1(lean_object*);
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___boxed(lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMutualDef___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_AddErrorMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_erase___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__1(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_Inhabited;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__2(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem(lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Closure_mkForall(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified___boxed(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__1;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__1(lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedRoot___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_pushMain(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__1;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_ClosureState_newLetDecls___default;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
lean_object* l_List_map___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__1(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___boxed(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_4__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabMutualDef___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified___rarg(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__2(lean_object*);
lean_object* l_List_foldr___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_erase___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l___private_Lean_Meta_Basic_37__instantiateForallAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_modifyUsedFVars___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__1;
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___at_Lean_Elab_Command_elabMutualDef___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___boxed(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_modifyUsedFVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instantiateMVarsAtPreDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders_match__1(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__2(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__1(lean_object*);
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDefView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_PreDefinition_inhabited___closed__1;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified___boxed(lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__2;
uint8_t l_Lean_Elab_isFreshInstanceName(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars_match__1(lean_object*);
lean_object* l_Lean_Elab_fixLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_662____closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Elab_Term_MutualClosure_pushMain___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5;
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_getKindForLetRecs___boxed(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getKindForLetRecs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_DefViewElabHeader_inhabited;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__2;
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__3;
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap___boxed(lean_object*);
lean_object* l___private_Lean_Meta_Basic_23__lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_FixPoint_run(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified___boxed(lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutualDef___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_Term_expandMatchAltsIntoMatch(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_DefViewElabHeader_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_PreDefinition_inhabited___closed__1;
x_4 = 0;
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Expr_Inhabited___closed__1;
x_8 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_5);
lean_ctor_set(x_8, 4, x_1);
lean_ctor_set(x_8, 5, x_6);
lean_ctor_set(x_8, 6, x_7);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set_uint8(x_8, sizeof(void*)*8, x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_DefViewElabHeader_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_DefViewElabHeader_inhabited___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot mix partial and non-partial definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
if (x_11 == 0)
{
if (x_12 == 0)
{
uint8_t x_19; 
x_19 = 1;
x_13 = x_19;
goto block_18;
}
else
{
uint8_t x_20; 
x_20 = 0;
x_13 = x_20;
goto block_18;
}
}
else
{
if (x_12 == 0)
{
uint8_t x_21; 
x_21 = 0;
x_13 = x_21;
goto block_18;
}
else
{
uint8_t x_22; 
x_22 = 1;
x_13 = x_22;
goto block_18;
}
}
block_18:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot mix computable and non-computable definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
if (x_11 == 0)
{
if (x_12 == 0)
{
uint8_t x_23; 
x_23 = 1;
x_13 = x_23;
goto block_22;
}
else
{
uint8_t x_24; 
x_24 = 0;
x_13 = x_24;
goto block_22;
}
}
else
{
if (x_12 == 0)
{
uint8_t x_25; 
x_25 = 0;
x_13 = x_25;
goto block_22;
}
else
{
uint8_t x_26; 
x_26 = 1;
x_13 = x_26;
goto block_22;
}
}
block_22:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_21 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1(x_1, x_2, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot mix unsafe and safe definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
if (x_10 == 0)
{
if (x_11 == 0)
{
uint8_t x_22; 
x_22 = 1;
x_12 = x_22;
goto block_21;
}
else
{
uint8_t x_23; 
x_23 = 0;
x_12 = x_23;
goto block_21;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_24; 
x_24 = 0;
x_12 = x_24;
goto block_21;
}
else
{
uint8_t x_25; 
x_25 = 1;
x_12 = x_25;
goto block_21;
}
}
block_21:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__3;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot mix theorems and definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = l_Lean_Elab_DefKind_isTheorem(x_1);
x_12 = l_Lean_Elab_DefKind_isTheorem(x_2);
if (x_11 == 0)
{
if (x_12 == 0)
{
uint8_t x_19; 
x_19 = 1;
x_13 = x_19;
goto block_18;
}
else
{
uint8_t x_20; 
x_20 = 0;
x_13 = x_20;
goto block_18;
}
}
else
{
if (x_12 == 0)
{
uint8_t x_21; 
x_21 = 0;
x_13 = x_21;
goto block_18;
}
else
{
uint8_t x_22; 
x_22 = 1;
x_13 = x_22;
goto block_18;
}
}
block_18:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot mix examples and definitions");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = l_Lean_Elab_DefKind_isExample(x_1);
x_11 = l_Lean_Elab_DefKind_isExample(x_2);
if (x_10 == 0)
{
if (x_11 == 0)
{
uint8_t x_22; 
x_22 = 1;
x_12 = x_22;
goto block_21;
}
else
{
uint8_t x_23; 
x_23 = 0;
x_12 = x_23;
goto block_21;
}
}
else
{
if (x_11 == 0)
{
uint8_t x_24; 
x_24 = 0;
x_12 = x_24;
goto block_21;
}
else
{
uint8_t x_25; 
x_25 = 1;
x_12 = x_25;
goto block_21;
}
}
block_21:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__3;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers(x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_17 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds(x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_4);
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
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("universe parameters mismatch");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually recursive definitions, ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_array_fget(x_1, x_12);
x_17 = lean_ctor_get(x_2, 4);
x_18 = lean_ctor_get(x_16, 4);
lean_inc(x_18);
x_19 = l_List_beq___main___at_Lean_OpenDecl_HasToString___spec__1(x_17, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_16);
x_20 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__3;
x_21 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_23, 1, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_21, 0, x_36);
return x_21;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_41 = x_37;
} else {
 lean_dec_ref(x_37);
 x_41 = lean_box(0);
}
x_42 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
x_49 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__1(x_2, x_16, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_16);
if (lean_obj_tag(x_49) == 0)
{
return x_49;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_51, 1);
x_54 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_51, 1, x_57);
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_49, 0, x_64);
return x_49;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_49, 0);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_49);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_72 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
return x_75;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'unsafe' subsumes 'partial'");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 2);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 0;
x_11 = x_23;
goto block_20;
}
else
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 3);
x_11 = x_24;
goto block_20;
}
block_20:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'noncomputable partial' is not allowed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 1);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 0;
x_11 = x_23;
goto block_20;
}
else
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 2);
x_11 = x_24;
goto block_20;
}
block_20:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'noncomputable unsafe' is not allowed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 1);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 0;
x_11 = x_23;
goto block_20;
}
else
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*2 + 3);
x_11 = x_24;
goto block_20;
}
block_20:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'theorem' subsumes 'noncomputable', code is not generated for theorems");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_21; uint8_t x_22; 
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_22 = l_Lean_Elab_DefKind_isTheorem(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 0;
x_11 = x_23;
goto block_20;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*2 + 1);
x_11 = x_25;
goto block_20;
}
block_20:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'partial' theorems are not allowed, 'partial' is a code generation directive");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_21; uint8_t x_22; 
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_22 = l_Lean_Elab_DefKind_isTheorem(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = 0;
x_11 = x_23;
goto block_20;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*2 + 2);
x_11 = x_25;
goto block_20;
}
block_20:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'unsafe' theorems are not allowed");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_20; uint8_t x_21; 
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_21 = l_Lean_Elab_DefKind_isTheorem(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = 0;
x_10 = x_22;
goto block_19;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*2 + 3);
x_10 = x_24;
goto block_19;
}
block_19:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7(x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__3;
x_14 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to infer definition type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__3;
x_11 = l_Lean_Elab_Term_registerCustomErrorIfMVar(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 4);
lean_inc(x_11);
lean_dec(x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkHole(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_elabType(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo(x_14, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_elabType(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 0;
x_28 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_29 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_27, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo(x_32, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
uint8_t x_41; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_24);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Environment_contains(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
lean_inc(x_2);
x_11 = l_Lean_mkPrivateName(x_2, x_1);
lean_inc(x_2);
x_12 = l_Lean_Environment_contains(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__2___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_12);
x_13 = l_Lean_Environment_contains(x_12, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__2(x_1, x_12, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
lean_inc(x_1);
x_16 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__3___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Elab_checkNotAlreadyDeclared___rarg___lambda__3___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
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
}
}
}
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
case 1:
{
lean_object* x_19; 
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_protectedExt;
lean_inc(x_2);
x_26 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_25, x_24, x_2);
x_27 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__4(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_st_ref_get(x_8, x_9);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_mkPrivateName(x_39, x_2);
lean_inc(x_40);
x_41 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_40);
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
}
}
}
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_inc(x_2);
x_12 = l_Lean_Name_append___main(x_1, x_2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_5);
x_14 = l_Lean_Elab_applyVisibility___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__3(x_13, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(x_13);
if (lean_obj_tag(x_15) == 1)
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_name_mk_string(x_19, x_18);
x_21 = l_Lean_Name_append___main(x_20, x_2);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_name_mk_string(x_26, x_25);
x_28 = l_Lean_Name_append___main(x_27, x_2);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = l_Lean_Elab_mkDeclName___rarg___lambda__1___closed__3;
x_33 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set(x_14, 0, x_36);
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_2);
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
}
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_3);
x_11 = l_Lean_extractMacroScopes(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Name_isAtomic(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Elab_isFreshInstanceName(x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = l_Lean_Elab_mkDeclName___rarg___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__3___closed__3;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___lambda__1(x_1, x_3, x_2, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___lambda__1(x_1, x_3, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = l_Lean_Syntax_getId(x_15);
x_19 = l_List_elem___main___at_Lean_NameHashSet_insert___spec__2(x_18, x_4);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_4);
x_3 = x_17;
x_4 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_9, 3);
x_24 = l_Lean_replaceRef(x_15, x_23);
lean_dec(x_15);
x_25 = l_Lean_replaceRef(x_24, x_23);
lean_dec(x_24);
x_26 = l_Lean_replaceRef(x_25, x_23);
lean_dec(x_23);
lean_dec(x_25);
lean_ctor_set(x_9, 3, x_26);
x_27 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__5(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
x_34 = lean_ctor_get(x_9, 2);
x_35 = lean_ctor_get(x_9, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_36 = l_Lean_replaceRef(x_15, x_35);
lean_dec(x_15);
x_37 = l_Lean_replaceRef(x_36, x_35);
lean_dec(x_36);
x_38 = l_Lean_replaceRef(x_37, x_35);
lean_dec(x_35);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_38);
x_40 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__5(x_18, x_5, x_6, x_7, x_8, x_39, x_10, x_11);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_10, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
x_16 = l_Lean_replaceRef(x_15, x_14);
lean_dec(x_15);
x_17 = l_Lean_replaceRef(x_16, x_14);
lean_dec(x_14);
lean_dec(x_16);
lean_ctor_set(x_10, 3, x_17);
x_18 = l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_5);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
x_36 = lean_ctor_get(x_10, 2);
x_37 = lean_ctor_get(x_10, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_38 = l_Lean_replaceRef(x_1, x_37);
x_39 = l_Lean_replaceRef(x_38, x_37);
lean_dec(x_38);
x_40 = l_Lean_replaceRef(x_39, x_37);
lean_dec(x_37);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_40);
x_42 = l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_41, x_11, x_12);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_5);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_45;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_52 = x_42;
} else {
 lean_dec_ref(x_42);
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
}
}
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Elab_expandDeclIdCore(x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_14, x_16);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_empty___closed__1;
x_22 = l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(x_19, x_18, x_20, x_21);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_5);
x_23 = l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__6(x_14, x_22, x_20, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_22);
lean_dec(x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___lambda__1(x_3, x_1, x_4, x_13, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec(x_14);
x_31 = l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___lambda__1(x_3, x_1, x_4, x_13, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_31;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_16);
x_17 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunType(x_16, x_8, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
lean_dec(x_1);
x_21 = lean_array_get_size(x_8);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_4);
lean_ctor_set(x_22, 3, x_5);
lean_ctor_set(x_22, 4, x_6);
lean_ctor_set(x_22, 5, x_21);
lean_ctor_set(x_22, 6, x_18);
lean_ctor_set(x_22, 7, x_16);
lean_ctor_set_uint8(x_22, sizeof(void*)*8, x_20);
x_23 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check(x_7, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_22);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
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
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = l_Lean_replaceRef(x_15, x_19);
x_21 = l_Lean_replaceRef(x_20, x_19);
lean_dec(x_20);
x_22 = l_Lean_replaceRef(x_21, x_19);
lean_dec(x_21);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_ctor_get(x_5, 2);
lean_inc(x_24);
x_25 = l_Lean_Elab_Term_getLevelNames(x_5, x_6, x_7, x_8, x_23, x_10, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_14, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_23);
lean_inc(x_5);
x_30 = l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1(x_24, x_26, x_28, x_29, x_5, x_6, x_7, x_8, x_23, x_10, x_27);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
x_37 = 2;
x_38 = 1;
lean_inc(x_10);
lean_inc(x_23);
lean_inc(x_5);
lean_inc(x_34);
x_39 = l_Lean_Elab_Term_applyAttributesAt(x_34, x_36, x_37, x_38, x_5, x_6, x_7, x_8, x_23, x_10, x_32);
lean_dec(x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_14, 3);
lean_inc(x_41);
x_42 = l_Lean_Syntax_getArgs(x_41);
lean_dec(x_41);
lean_inc(x_4);
lean_inc(x_35);
x_43 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___lambda__1___boxed), 15, 7);
lean_closure_set(x_43, 0, x_14);
lean_closure_set(x_43, 1, x_15);
lean_closure_set(x_43, 2, x_29);
lean_closure_set(x_43, 3, x_33);
lean_closure_set(x_43, 4, x_34);
lean_closure_set(x_43, 5, x_35);
lean_closure_set(x_43, 6, x_4);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_44, 0, x_42);
lean_closure_set(x_44, 1, x_43);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Elab_Term_withLevelNames___rarg(x_35, x_44, x_5, x_6, x_7, x_8, x_23, x_10, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_push(x_4, x_46);
x_49 = 1;
x_50 = x_3 + x_49;
x_3 = x_50;
x_4 = x_48;
x_11 = x_47;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_45, 0);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
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
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_39);
if (x_56 == 0)
{
return x_39;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
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
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_30);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_30, 0);
x_62 = lean_ctor_get(x_30, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_30);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_empty___closed__1;
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_checkNotAlreadyDeclared___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_applyVisibility___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_Lean_Elab_applyVisibility___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_mkDeclName___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_expandDeclId___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_16;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___spec__7(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = lean_array_push(x_2, x_5);
x_16 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg(x_3, x_4, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_array_fget(x_1, x_3);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 6);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg___lambda__1___boxed), 12, 4);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_1);
lean_closure_set(x_18, 3, x_2);
x_19 = 4;
x_20 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__3___rarg(x_16, x_19, x_17, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_empty___closed__1;
x_12 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls_loop___rarg(x_1, x_2, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("declValEqns");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected definition value");
return x_1;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_mkDefViewOfConstant___closed__8;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__2;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__3;
x_9 = l_Lean_Macro_throwError___rarg(x_1, x_8, x_2, x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = 0;
x_13 = l_Lean_Elab_Term_expandMatchAltsIntoMatch(x_1, x_11, x_12, x_2, x_3);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
x_15 = lean_st_ref_get(x_8, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_2);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Util_0__Lean_Elab_expandMacro_x3f___boxed), 4, 1);
lean_closure_set(x_19, 0, x_2);
x_20 = x_19;
x_21 = lean_environment_main_module(x_2);
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_11);
lean_ctor_set(x_22, 3, x_13);
lean_ctor_set(x_22, 4, x_14);
x_23 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm(x_1, x_22, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_take(x_8, x_17);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
lean_ctor_set(x_27, 1, x_25);
x_31 = lean_st_ref_set(x_8, x_27, x_28);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_24);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 2);
x_38 = lean_ctor_get(x_27, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_st_ref_set(x_8, x_39, x_28);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_23, 0);
lean_inc(x_44);
lean_dec(x_23);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lean_throwErrorAt___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__2___rarg(x_45, x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_45);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_3);
x_50 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabFun___spec__2___rarg(x_17);
return x_50;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = lean_box(0);
x_13 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_11, x_13, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabFun___spec__1(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 6);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__3), 10, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg(x_10, x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_ReaderT_lift___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 7);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__2___boxed), 9, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__2;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 9, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_24 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__4), 9, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 9, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Term_withLevelNames___rarg), 9, 2);
lean_closure_set(x_26, 0, x_19);
lean_closure_set(x_26, 1, x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_Elab_Term_withDeclName___rarg(x_18, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_1, x_30);
x_32 = x_28;
x_33 = lean_array_fset(x_16, x_1, x_32);
lean_dec(x_1);
x_1 = x_31;
x_2 = x_33;
x_9 = x_29;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1), 9, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = x_11;
x_13 = lean_apply_7(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = lean_ctor_get(x_15, 6);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Term_collectUsedFVars(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
x_10 = x_18;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = l_Lean_Elab_Term_collectUsedFVars(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
x_10 = x_17;
goto _start;
}
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 7);
lean_inc(x_14);
x_15 = l_Lean_Elab_Term_collectUsedFVars(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_12, 8);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_Elab_Term_collectUsedFVars(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_1 = x_13;
x_9 = x_19;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__1(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__2(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_HashSet_Inhabited___closed__1;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_collectUsed(x_2, x_3, x_4, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_14, x_17);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_removeUnused(x_1, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
return x_21;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_5 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = lean_apply_8(x_6, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_apply_1(x_6, x_21);
x_23 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabBinders___spec__2___rarg(x_19, x_20, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg___boxed), 13, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
lean_dec(x_7);
x_9 = l_Lean_Elab_DefKind_isExample(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
uint8_t l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___spec__1(x_1, x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
lean_dec(x_7);
x_9 = l_Lean_Elab_DefKind_isTheorem(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
uint8_t l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___spec__1(x_1, x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 6);
x_11 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 6, x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_1, 6, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = lean_ctor_get(x_1, 4);
x_23 = lean_ctor_get(x_1, 5);
x_24 = lean_ctor_get(x_1, 6);
x_25 = lean_ctor_get(x_1, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_26 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set(x_30, 5, x_23);
lean_ctor_set(x_30, 6, x_27);
lean_ctor_set(x_30, 7, x_25);
lean_ctor_set_uint8(x_30, sizeof(void*)*8, x_19);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 7);
x_11 = lean_ctor_get(x_1, 8);
x_12 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 8, x_17);
lean_ctor_set(x_1, 7, x_13);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 8, x_18);
lean_ctor_set(x_1, 7, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_ctor_get(x_1, 4);
x_26 = lean_ctor_get(x_1, 5);
x_27 = lean_ctor_get(x_1, 6);
x_28 = lean_ctor_get(x_1, 7);
x_29 = lean_ctor_get(x_1, 8);
x_30 = lean_ctor_get(x_1, 9);
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
lean_dec(x_1);
x_31 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
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
x_38 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_22);
lean_ctor_set(x_38, 2, x_23);
lean_ctor_set(x_38, 3, x_24);
lean_ctor_set(x_38, 4, x_25);
lean_ctor_set(x_38, 5, x_26);
lean_ctor_set(x_38, 6, x_27);
lean_ctor_set(x_38, 7, x_32);
lean_ctor_set(x_38, 8, x_35);
lean_ctor_set(x_38, 9, x_30);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_2(x_2, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun_match__2___rarg), 3, 0);
return x_2;
}
}
uint8_t l_List_foldr___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_eq(x_7, x_1);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; size_t x_107; size_t x_108; lean_object* x_109; size_t x_110; uint8_t x_111; 
x_107 = lean_ptr_addr(x_4);
x_108 = x_3 == 0 ? 0 : x_107 % x_3;
x_109 = lean_array_uget(x_5, x_108);
x_110 = lean_ptr_addr(x_109);
lean_dec(x_109);
x_111 = x_110 == x_107;
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
lean_inc(x_4);
x_112 = lean_array_uset(x_5, x_108, x_4);
x_113 = 0;
x_6 = x_113;
x_7 = x_112;
goto block_106;
}
else
{
uint8_t x_114; 
x_114 = 1;
x_6 = x_114;
x_7 = x_5;
goto block_106;
}
block_106:
{
lean_object* x_8; 
if (x_6 == 0)
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_4, 0);
lean_inc(x_94);
x_95 = l_Array_contains___at_Lean_Meta_addInstanceEntry___spec__11(x_1, x_4);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 0;
x_97 = l_List_foldr___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__1(x_94, x_96, x_2);
lean_dec(x_94);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_box(0);
x_8 = x_98;
goto block_93;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_4);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_7);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_94);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_4);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_7);
return x_102;
}
}
else
{
lean_object* x_103; 
x_103 = lean_box(0);
x_8 = x_103;
goto block_93;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_4);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_7);
return x_105;
}
block_93:
{
lean_dec(x_8);
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(x_1, x_2, x_3, x_9, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_4 = x_10;
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_22 = x_12;
} else {
 lean_dec_ref(x_12);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
case 6:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 2);
lean_inc(x_26);
lean_dec(x_4);
x_27 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(x_1, x_2, x_3, x_25, x_7);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_4 = x_26;
x_5 = x_29;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_26);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_38 = x_28;
} else {
 lean_dec_ref(x_28);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
}
}
case 7:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 2);
lean_inc(x_42);
lean_dec(x_4);
x_43 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(x_1, x_2, x_3, x_41, x_7);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_4 = x_42;
x_5 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_42);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_54 = x_44;
} else {
 lean_dec_ref(x_44);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
}
case 8:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_4, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_4, 3);
lean_inc(x_59);
lean_dec(x_4);
x_60 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(x_1, x_2, x_3, x_57, x_7);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(x_1, x_2, x_3, x_58, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_4 = x_59;
x_5 = x_65;
goto _start;
}
else
{
uint8_t x_67; 
lean_dec(x_59);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_63, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_63, 0, x_71);
return x_63;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_dec(x_63);
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_74 = x_64;
} else {
 lean_dec_ref(x_64);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_59);
lean_dec(x_58);
x_77 = !lean_is_exclusive(x_60);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_60, 0);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_60;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_61, 0);
lean_inc(x_80);
lean_dec(x_61);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_60, 0, x_81);
return x_60;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_60, 1);
lean_inc(x_82);
lean_dec(x_60);
x_83 = lean_ctor_get(x_61, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_84 = x_61;
} else {
 lean_dec_ref(x_61);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
}
}
case 10:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_4, 1);
lean_inc(x_87);
lean_dec(x_4);
x_4 = x_87;
x_5 = x_7;
goto _start;
}
case 11:
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_4, 2);
lean_inc(x_89);
lean_dec(x_4);
x_4 = x_89;
x_5 = x_7;
goto _start;
}
default: 
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_4);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_7);
return x_92;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 8192;
x_5 = l_Lean_Expr_FindImpl_initCache;
x_6 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(x_2, x_3, x_4, x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; 
lean_free_object(x_7);
lean_dec(x_10);
x_12 = lean_box(0);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
}
}
}
}
lean_object* l_List_foldr___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___spec__2(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_findLocalDecl_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_local_ctx_find(x_9, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_name_eq(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown function");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_findLocalDecl_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___lambda__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_1);
x_16 = l_List_findSome_x3f___main___rarg(x_15, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
x_17 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__3;
x_18 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___lambda__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_1);
x_22 = l_List_findSome_x3f___main___rarg(x_21, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__3;
x_24 = l_Lean_throwError___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__3___rarg(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
lean_dec(x_3);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = l_Lean_LocalDecl_userName(x_29);
lean_dec(x_29);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_dec(x_10);
x_32 = lean_ctor_get(x_11, 0);
lean_inc(x_32);
lean_dec(x_11);
x_33 = l_Lean_LocalDecl_userName(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_findLocalDecl_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_findLocalDecl_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid type in 'let rec', it uses '");
return x_1;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' which is being defined simultaneously");
return x_1;
}
}
static lean_object* _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_ctor_get(x_13, 7);
lean_inc(x_15);
x_16 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_typeHasRecFun(x_15, x_1, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_13);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_4);
x_19 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName(x_18, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwErrorAt___at___private_Lean_Elab_Quotation_0__Lean_Elab_Term_Quotation_quoteSyntax___spec__2___rarg(x_22, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_6);
lean_dec(x_22);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1(x_1, x_2, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_7, x_8);
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_4 < x_3;
if (x_6 == 0)
{
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_4);
lean_inc(x_1);
x_8 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_7, x_1);
x_9 = 1;
x_10 = x_4 + x_9;
x_4 = x_10;
x_5 = x_8;
goto _start;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 9);
x_5 = l_Lean_MetavarContext_getDelayedRoot___main(x_1, x_2);
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_inc(x_2);
x_10 = l_List_findSome_x3f___main___rarg(x_9, x_2);
if (lean_obj_tag(x_10) == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = x_5 + x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_6, x_14, x_15);
x_17 = 1;
x_18 = x_5 + x_17;
x_5 = x_18;
x_6 = x_16;
goto _start;
}
}
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 8);
lean_inc(x_8);
x_9 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
lean_inc(x_8);
x_10 = l_Lean_CollectFVars_main___main(x_8, x_9);
x_11 = lean_ctor_get(x_6, 7);
lean_inc(x_11);
x_12 = l_Lean_CollectFVars_main___main(x_11, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_getMVarsImp___closed__1;
x_15 = l_Lean_Expr_collectMVars(x_14, x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3(x_1, x_2, x_16, x_18, x_3, x_13);
lean_dec(x_16);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
x_21 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_20, x_19);
x_4 = x_7;
x_5 = x_21;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Lean_NameSet_empty;
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__1(x_2, x_6, x_7, x_8);
x_10 = lean_box(0);
x_11 = lean_array_get_size(x_3);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__2(x_9, x_3, x_12, x_7, x_10);
lean_inc(x_4);
x_14 = l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__4(x_1, x_4, x_7, x_4, x_13);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___spec__4(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_MutualClosure_FixPoint_State_usedFVarsMap___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Term_MutualClosure_FixPoint_State_modified___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_3);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*1, x_3);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = 1;
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap___rarg), 1, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_modifyUsedFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_3, 0, x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_apply_1(x_1, x_9);
x_12 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_modifyUsedFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_modifyUsedFVars(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1(x_1, x_6, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_NameSet_contains(x_10, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_markModified___rarg(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_10, x_7, x_15);
x_1 = x_16;
x_2 = x_8;
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_7);
x_1 = x_10;
x_2 = x_8;
x_4 = x_11;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 3);
x_11 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2(x_1, x_2, x_3, x_8, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_name_eq(x_1, x_9);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1(x_2, x_9);
if (lean_obj_tag(x_15) == 0)
{
x_3 = x_12;
x_4 = x_10;
x_6 = x_13;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_merge___spec__1(x_12, x_17, x_5, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_19;
x_4 = x_10;
x_6 = x_20;
goto _start;
}
}
else
{
x_3 = x_12;
x_4 = x_10;
x_6 = x_13;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_getUsedFVarsMap___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1(x_6, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_box(0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_10);
x_11 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2(x_1, x_6, x_10, x_10, x_2, x_7);
lean_dec(x_10);
lean_dec(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___lambda__1), 3, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_12);
x_15 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_modifyUsedFVars(x_14, x_2, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1(x_16, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_21);
x_22 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2(x_1, x_16, x_21, x_21, x_2, x_17);
lean_dec(x_21);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___lambda__1), 3, 2);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_23);
x_26 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_modifyUsedFVars(x_25, x_2, x_24);
return x_26;
}
}
}
}
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_RBNode_foldM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf(x_6, x_2, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_resetModified___rarg(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_5 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___spec__1(x_1, x_1, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_isModified___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_2 = x_16;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_FixPoint_run_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_FixPoint_run_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_MutualClosure_FixPoint_run_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_FixPoint_run(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = 0;
x_4 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*1, x_3);
x_5 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_fixpoint___rarg(x_1, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__1(lean_object* x_1) {
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__1(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_2);
x_8 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__2(x_1, x_2, x_3, x_5);
lean_inc(x_2);
x_9 = l_Lean_LocalContext_contains(x_2, x_6);
if (x_9 == 0)
{
lean_dec(x_6);
x_3 = x_8;
x_4 = x_7;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_1, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_8, x_6);
x_3 = x_12;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_6);
x_3 = x_8;
x_4 = x_7;
goto _start;
}
}
}
}
}
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 3);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_2);
x_8 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__3(x_1, x_2, x_3, x_5);
lean_inc(x_2);
x_9 = l_Lean_LocalContext_contains(x_2, x_6);
if (x_9 == 0)
{
lean_dec(x_6);
x_3 = x_8;
x_4 = x_7;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_1, x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_8, x_6);
x_3 = x_12;
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_6);
x_3 = x_8;
x_4 = x_7;
goto _start;
}
}
}
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 5);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_FixPoint_updateUsedVarsOf___spec__1(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_NameSet_Inhabited;
x_11 = l_Option_get_x21___rarg___closed__3;
x_12 = lean_panic_fn(x_10, x_11);
x_13 = l_Array_empty___closed__1;
x_14 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__2(x_1, x_7, x_13, x_12);
x_15 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_8, x_14);
x_3 = x_6;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l_Array_empty___closed__1;
x_19 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__3(x_1, x_7, x_18, x_17);
x_20 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_8, x_19);
x_3 = x_6;
x_4 = x_20;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_5);
x_6 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkInitialUsedFVarsMap(x_1, x_2, x_3, x_5);
lean_inc(x_5);
x_7 = l_List_map___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__1(x_5);
x_8 = l_Lean_Elab_Term_MutualClosure_FixPoint_run(x_7, x_6);
x_9 = lean_box(0);
x_10 = l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__4(x_4, x_8, x_5, x_9);
lean_dec(x_8);
return x_10;
}
}
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forInAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_MutualClosure_ClosureState_newLocalDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_MutualClosure_ClosureState_localDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_MutualClosure_ClosureState_newLetDecls___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_MutualClosure_ClosureState_exprArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_5);
lean_inc(x_1);
x_9 = l_Lean_LocalContext_get_x21(x_1, x_5);
x_10 = l_Lean_LocalDecl_index(x_9);
lean_dec(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_11 = l_Lean_LocalContext_get_x21(x_1, x_8);
x_12 = l_Lean_LocalDecl_index(x_11);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
if (x_13 == 0)
{
lean_dec(x_8);
x_4 = x_15;
goto _start;
}
else
{
lean_dec(x_5);
x_4 = x_15;
x_5 = x_8;
goto _start;
}
}
}
}
lean_object* l_Array_getMax_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__2(x_1, x_2, x_2, x_8, x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_getMax_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_getMax_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_getMax_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = l_Lean_Meta_check(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_10);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars___spec__1(x_1, x_3);
x_7 = l_Array_contains___at___private_Lean_Class_1__checkOutParam___main___spec__1(x_6, x_4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_array_push(x_6, x_4);
x_1 = x_8;
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_4);
x_1 = x_6;
x_2 = x_5;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Std_RBNode_fold___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars___spec__1(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 3);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_2);
x_24 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_15);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_5);
x_25 = lean_array_push(x_21, x_24);
x_26 = l_Lean_mkFVar(x_2);
x_27 = lean_array_push(x_22, x_26);
lean_ctor_set(x_18, 3, x_27);
lean_ctor_set(x_18, 0, x_25);
x_28 = lean_st_ref_set(x_6, x_18, x_19);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
x_32 = l_Lean_CollectFVars_main___main(x_15, x_31);
x_33 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars(x_1, x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
x_36 = l_Lean_CollectFVars_main___main(x_15, x_35);
x_37 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars(x_1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
x_41 = lean_ctor_get(x_18, 2);
x_42 = lean_ctor_get(x_18, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_2);
x_44 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_2);
lean_ctor_set(x_44, 2, x_3);
lean_ctor_set(x_44, 3, x_15);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_5);
x_45 = lean_array_push(x_39, x_44);
x_46 = l_Lean_mkFVar(x_2);
x_47 = lean_array_push(x_42, x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_st_ref_set(x_6, x_48, x_19);
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
x_52 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
x_53 = l_Lean_CollectFVars_main___main(x_15, x_52);
x_54 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars(x_1, x_53);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushLocalDecl(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_5(x_2, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
lean_dec(x_1);
x_17 = lean_box(x_16);
x_18 = lean_apply_6(x_3, x_11, x_12, x_13, x_14, x_15, x_17);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_erase___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_indexOfAux___main___at_Lean_LocalContext_erase___spec__3(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Array_feraseIdx___rarg(x_1, x_5);
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_local_ctx_find(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___rarg___boxed), 4, 0);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
lean_inc(x_1);
x_12 = l_Lean_replaceFVarIdAtLocalDecl(x_1, x_2, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_10, x_3, x_15);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
lean_inc(x_1);
x_12 = l_Lean_replaceFVarIdAtLocalDecl(x_1, x_2, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_10, x_3, x_15);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_13);
lean_inc(x_11);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_PersistentArray_push___rarg(x_22, x_24);
lean_ctor_set(x_17, 0, x_25);
x_26 = lean_st_ref_set(x_9, x_16, x_18);
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
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_13);
lean_inc(x_11);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Std_PersistentArray_push___rarg(x_34, x_36);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_33);
lean_ctor_set(x_16, 3, x_38);
x_39 = lean_st_ref_set(x_9, x_16, x_18);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
x_46 = lean_ctor_get(x_16, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_47 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_49 = x_17;
} else {
 lean_dec_ref(x_17);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_13);
lean_inc(x_11);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Std_PersistentArray_push___rarg(x_48, x_51);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 1, 1);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_47);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_46);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_9, x_54, x_18);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_checkTraceOption(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkClosure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_662____closed__2;
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toProcess: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", maxVar: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = l_Array_getMax_x3f___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pickMaxFVar_x3f___spec__1(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_118; lean_object* x_119; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_140 = lean_st_ref_get(x_8, x_9);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_141, 3);
lean_inc(x_142);
lean_dec(x_141);
x_143 = lean_ctor_get_uint8(x_142, sizeof(void*)*1);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = 0;
x_118 = x_145;
x_119 = x_144;
goto block_139;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_147 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__2;
x_148 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__7(x_147, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_unbox(x_149);
lean_dec(x_149);
x_118 = x_151;
x_119 = x_150;
goto block_139;
}
block_117:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Array_erase___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__1(x_1, x_14);
lean_inc(x_5);
lean_inc(x_14);
x_17 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 3);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushLocalDecl(x_16, x_14, x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_1 = x_24;
x_9 = x_25;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_110; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = lean_ctor_get(x_18, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_18, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 4);
lean_inc(x_34);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 lean_ctor_release(x_18, 4);
 x_35 = x_18;
} else {
 lean_dec_ref(x_18);
 x_35 = lean_box(0);
}
x_36 = l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___rarg(x_6, x_7, x_8, x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_110 = l_Lean_NameSet_contains(x_37, x_14);
lean_dec(x_37);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = 1;
x_39 = x_111;
goto block_109;
}
else
{
uint8_t x_112; 
x_112 = 0;
x_39 = x_112;
goto block_109;
}
block_109:
{
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess(x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_preprocess(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_st_ref_take(x_2, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_50 = lean_ctor_get(x_47, 0);
x_51 = lean_ctor_get(x_47, 1);
x_52 = lean_ctor_get(x_47, 2);
x_53 = x_50;
x_54 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
x_55 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__4(x_14, x_44, x_54, x_53);
x_56 = x_55;
x_57 = x_51;
lean_inc(x_14);
x_58 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__5(x_14, x_44, x_54, x_57);
x_59 = x_58;
x_60 = 0;
lean_inc(x_44);
lean_inc(x_41);
if (lean_is_scalar(x_35)) {
 x_61 = lean_alloc_ctor(1, 5, 1);
} else {
 x_61 = x_35;
}
lean_ctor_set(x_61, 0, x_54);
lean_ctor_set(x_61, 1, x_14);
lean_ctor_set(x_61, 2, x_32);
lean_ctor_set(x_61, 3, x_41);
lean_ctor_set(x_61, 4, x_44);
lean_ctor_set_uint8(x_61, sizeof(void*)*5, x_60);
x_62 = lean_array_push(x_52, x_61);
lean_ctor_set(x_47, 2, x_62);
lean_ctor_set(x_47, 1, x_59);
lean_ctor_set(x_47, 0, x_56);
x_63 = lean_st_ref_set(x_2, x_47, x_48);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
x_66 = l_Lean_CollectFVars_main___main(x_41, x_65);
x_67 = l_Lean_CollectFVars_main___main(x_44, x_66);
x_68 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars(x_16, x_67);
x_1 = x_68;
x_9 = x_64;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_ctor_get(x_47, 1);
x_72 = lean_ctor_get(x_47, 2);
x_73 = lean_ctor_get(x_47, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_47);
x_74 = x_70;
x_75 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
x_76 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__4(x_14, x_44, x_75, x_74);
x_77 = x_76;
x_78 = x_71;
lean_inc(x_14);
x_79 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__5(x_14, x_44, x_75, x_78);
x_80 = x_79;
x_81 = 0;
lean_inc(x_44);
lean_inc(x_41);
if (lean_is_scalar(x_35)) {
 x_82 = lean_alloc_ctor(1, 5, 1);
} else {
 x_82 = x_35;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_14);
lean_ctor_set(x_82, 2, x_32);
lean_ctor_set(x_82, 3, x_41);
lean_ctor_set(x_82, 4, x_44);
lean_ctor_set_uint8(x_82, sizeof(void*)*5, x_81);
x_83 = lean_array_push(x_72, x_82);
x_84 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_84, 3, x_73);
x_85 = lean_st_ref_set(x_2, x_84, x_48);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1;
x_88 = l_Lean_CollectFVars_main___main(x_41, x_87);
x_89 = l_Lean_CollectFVars_main___main(x_44, x_88);
x_90 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushNewVars(x_16, x_89);
x_1 = x_90;
x_9 = x_86;
goto _start;
}
}
else
{
uint8_t x_92; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_92 = !lean_is_exclusive(x_43);
if (x_92 == 0)
{
return x_43;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_43, 0);
x_94 = lean_ctor_get(x_43, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_43);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_96 = !lean_is_exclusive(x_40);
if (x_96 == 0)
{
return x_40;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_40, 0);
x_98 = lean_ctor_get(x_40, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_40);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; lean_object* x_101; 
lean_dec(x_35);
lean_dec(x_34);
x_100 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_101 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_pushLocalDecl(x_16, x_14, x_32, x_33, x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_1 = x_102;
x_9 = x_103;
goto _start;
}
else
{
uint8_t x_105; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_105 = !lean_is_exclusive(x_101);
if (x_105 == 0)
{
return x_101;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_113 = !lean_is_exclusive(x_17);
if (x_113 == 0)
{
return x_17;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_17, 0);
x_115 = lean_ctor_get(x_17, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_17);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
block_139:
{
if (x_118 == 0)
{
x_15 = x_119;
goto block_117;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_inc(x_1);
x_120 = x_1;
x_121 = lean_unsigned_to_nat(0u);
x_122 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_121, x_120);
x_123 = x_122;
x_124 = l_Array_toList___rarg(x_123);
lean_dec(x_123);
x_125 = l_List_map___main___at_Lean_MessageData_hasCoeOfListExpr___spec__1(x_124);
x_126 = l_Lean_MessageData_ofList(x_125);
lean_dec(x_125);
x_127 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__4;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__6;
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_14);
x_131 = l_Lean_mkFVar(x_14);
x_132 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__2;
x_137 = l_Lean_addTrace___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__6(x_136, x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_119);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_15 = x_138;
goto block_117;
}
}
}
}
}
lean_object* l_Array_erase___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_erase___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_getZetaFVarIds___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Array_empty___closed__1;
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_10);
x_12 = lean_st_mk_ref(x_11, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_13, x_16);
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 2);
x_23 = lean_ctor_get(x_19, 3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_reverseAux___main___rarg(x_21, x_24);
x_26 = l_Array_reverseAux___main___rarg(x_22, x_24);
x_27 = l_Array_reverseAux___main___rarg(x_23, x_24);
lean_ctor_set(x_19, 3, x_27);
lean_ctor_set(x_19, 2, x_26);
lean_ctor_set(x_19, 0, x_25);
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
x_30 = lean_ctor_get(x_19, 2);
x_31 = lean_ctor_get(x_19, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_reverseAux___main___rarg(x_28, x_32);
x_34 = l_Array_reverseAux___main___rarg(x_30, x_32);
x_35 = l_Array_reverseAux___main___rarg(x_31, x_32);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_17, 0, x_36);
return x_17;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_reverseAux___main___rarg(x_39, x_44);
x_46 = l_Array_reverseAux___main___rarg(x_41, x_44);
x_47 = l_Array_reverseAux___main___rarg(x_42, x_44);
if (lean_is_scalar(x_43)) {
 x_48 = lean_alloc_ctor(0, 4, 0);
} else {
 x_48 = x_43;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_13);
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
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_instantiateForall___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_Basic_37__instantiateForallAux___main(x_2, x_10, x_1, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_LocalContext_get_x21(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_9, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__2___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_23__lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__3___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 7);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Meta_Basic_37__instantiateForallAux___main(x_5, x_15, x_14, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
x_20 = x_5;
x_21 = l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__2(x_19, x_15, x_20);
x_22 = x_21;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureFor(x_2, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_29);
lean_dec(x_24);
lean_inc(x_28);
x_30 = l_Lean_Meta_Closure_mkForall(x_28, x_17);
lean_dec(x_17);
lean_inc(x_27);
x_31 = l_Lean_Meta_Closure_mkForall(x_27, x_30);
lean_dec(x_30);
x_32 = l_Lean_Meta_Closure_mkLambda(x_28, x_6);
x_33 = l_Lean_Meta_Closure_mkLambda(x_27, x_32);
lean_dec(x_32);
x_34 = lean_ctor_get(x_1, 4);
lean_inc(x_34);
x_35 = lean_box(0);
lean_inc(x_34);
x_36 = l_Lean_mkConst(x_34, x_35);
x_37 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_29, x_29, x_15, x_36);
lean_dec(x_29);
x_38 = lean_ctor_get(x_1, 9);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_38);
x_39 = l_Lean_Meta_assignExprMVar___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_resumePostponed___spec__4(x_38, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 3);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 4, x_34);
lean_ctor_set(x_46, 5, x_3);
lean_ctor_set(x_46, 6, x_4);
lean_ctor_set(x_46, 7, x_31);
lean_ctor_set(x_46, 8, x_33);
lean_ctor_set(x_46, 9, x_38);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_37);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 3);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_51);
lean_ctor_set(x_53, 3, x_52);
lean_ctor_set(x_53, 4, x_34);
lean_ctor_set(x_53, 5, x_3);
lean_ctor_set(x_53, 6, x_4);
lean_ctor_set(x_53, 7, x_31);
lean_ctor_set(x_53, 8, x_33);
lean_ctor_set(x_53, 9, x_38);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_37);
lean_ctor_set(x_54, 2, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_23);
if (x_56 == 0)
{
return x_23;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_23, 0);
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_23);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_16);
if (x_60 == 0)
{
return x_16;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 6);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___lambda__1___boxed), 13, 4);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__3___rarg), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabBinders___spec__2___rarg(x_10, x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
lean_object* l_Lean_Meta_instantiateForall___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_instantiateForall___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__1(x_1, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Array_empty___closed__1;
x_18 = l_Option_get_x21___rarg___closed__3;
x_19 = lean_panic_fn(x_17, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor(x_13, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_2, 1, x_25);
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_2, 1, x_26);
lean_ctor_set(x_2, 0, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_21);
lean_free_object(x_2);
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
uint8_t x_33; 
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_38 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor(x_13, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set(x_41, 0, x_2);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_41, 0);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_41);
lean_ctor_set(x_2, 1, x_44);
lean_ctor_set(x_2, 0, x_39);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_39);
lean_free_object(x_2);
x_47 = !lean_is_exclusive(x_41);
if (x_47 == 0)
{
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
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
lean_free_object(x_2);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__1(x_1, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l_Array_empty___closed__1;
x_60 = l_Option_get_x21___rarg___closed__3;
x_61 = lean_panic_fn(x_59, x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_62 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor(x_55, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_1, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_77 = x_62;
} else {
 lean_dec_ref(x_62);
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
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_58, 0);
lean_inc(x_79);
lean_dec(x_58);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosureFor(x_55, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_1, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_81);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_95 = x_80;
} else {
 lean_dec_ref(x_80);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
x_11 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_12 = l_Lean_Expr_Inhabited;
x_13 = lean_array_get(x_12, x_3, x_11);
x_14 = l_Lean_Expr_fvarId_x21(x_13);
lean_dec(x_13);
x_15 = l_Lean_Elab_DefViewElabHeader_inhabited;
x_16 = lean_array_get(x_15, x_2, x_11);
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = l_Lean_mkConst(x_17, x_18);
x_20 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_1, x_1, x_7, x_19);
x_21 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_14, x_20);
x_5 = x_10;
x_6 = x_21;
goto _start;
}
else
{
lean_dec(x_5);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_4);
lean_inc(x_5);
x_6 = l_Nat_foldAux___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___spec__1(x_2, x_3, x_4, x_5, x_5, x_1);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldAux___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_1, x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_MutualClosure_Replacement_apply_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Util_SCC_8__sccAux___main___rarg___closed__1;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_159; lean_object* x_160; size_t x_161; uint8_t x_162; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_159 = lean_ctor_get(x_4, 0);
lean_inc(x_159);
x_160 = lean_array_uget(x_159, x_6);
x_161 = lean_ptr_addr(x_160);
lean_dec(x_160);
x_162 = x_161 == x_5;
if (x_162 == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_3, 0);
lean_inc(x_163);
x_164 = l_Std_RBNode_find___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__1(x_1, x_163);
lean_dec(x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
lean_dec(x_159);
x_165 = lean_box(0);
x_7 = x_165;
goto block_158;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_array_uset(x_159, x_6, x_3);
x_168 = lean_ctor_get(x_4, 1);
lean_inc(x_168);
lean_dec(x_4);
lean_inc(x_166);
x_169 = lean_array_uset(x_168, x_6, x_166);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
else
{
lean_object* x_172; 
lean_dec(x_159);
x_172 = lean_box(0);
x_7 = x_172;
goto block_158;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_159);
lean_dec(x_3);
x_173 = lean_ctor_get(x_4, 1);
lean_inc(x_173);
x_174 = lean_array_uget(x_173, x_6);
lean_dec(x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_4);
return x_175;
}
block_158:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_8, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_inc(x_3);
x_18 = lean_array_uset(x_17, x_6, x_3);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_expr_update_app(x_3, x_11, x_15);
lean_inc(x_20);
x_21 = lean_array_uset(x_19, x_6, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_inc(x_3);
x_26 = lean_array_uset(x_25, x_6, x_3);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_expr_update_app(x_3, x_11, x_23);
lean_inc(x_28);
x_29 = lean_array_uset(x_27, x_6, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
case 6:
{
lean_object* x_32; lean_object* x_33; uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 2);
lean_inc(x_33);
x_34 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_35 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_32, x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_33, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_inc(x_3);
x_43 = lean_array_uset(x_42, x_6, x_3);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = (uint8_t)((x_34 << 24) >> 61);
x_46 = lean_expr_update_lambda(x_3, x_45, x_36, x_40);
lean_inc(x_46);
x_47 = lean_array_uset(x_44, x_6, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_38, 1, x_48);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_inc(x_3);
x_52 = lean_array_uset(x_51, x_6, x_3);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = (uint8_t)((x_34 << 24) >> 61);
x_55 = lean_expr_update_lambda(x_3, x_54, x_36, x_49);
lean_inc(x_55);
x_56 = lean_array_uset(x_53, x_6, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_62 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_59, x_4);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_60, x_64);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_inc(x_3);
x_70 = lean_array_uset(x_69, x_6, x_3);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = (uint8_t)((x_61 << 24) >> 61);
x_73 = lean_expr_update_forall(x_3, x_72, x_63, x_67);
lean_inc(x_73);
x_74 = lean_array_uset(x_71, x_6, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_65, 1, x_75);
lean_ctor_set(x_65, 0, x_73);
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_65, 0);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_65);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_inc(x_3);
x_79 = lean_array_uset(x_78, x_6, x_3);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = (uint8_t)((x_61 << 24) >> 61);
x_82 = lean_expr_update_forall(x_3, x_81, x_63, x_76);
lean_inc(x_82);
x_83 = lean_array_uset(x_80, x_6, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
case 8:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 3);
lean_inc(x_88);
x_89 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_86, x_4);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_87, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_88, x_94);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_95, 1);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_inc(x_3);
x_100 = lean_array_uset(x_99, x_6, x_3);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_expr_update_let(x_3, x_90, x_93, x_97);
lean_inc(x_102);
x_103 = lean_array_uset(x_101, x_6, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_95, 1, x_104);
lean_ctor_set(x_95, 0, x_102);
return x_95;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_95, 0);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_95);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_inc(x_3);
x_108 = lean_array_uset(x_107, x_6, x_3);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_expr_update_let(x_3, x_90, x_93, x_105);
lean_inc(x_110);
x_111 = lean_array_uset(x_109, x_6, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
case 10:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_3, 1);
lean_inc(x_114);
x_115 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_114, x_4);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_6, x_3);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_expr_update_mdata(x_3, x_117);
lean_inc(x_122);
x_123 = lean_array_uset(x_121, x_6, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_115, 1, x_124);
lean_ctor_set(x_115, 0, x_122);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_inc(x_3);
x_128 = lean_array_uset(x_127, x_6, x_3);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_expr_update_mdata(x_3, x_125);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_6, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
case 11:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_3, 2);
lean_inc(x_134);
x_135 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_2, x_134, x_4);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_inc(x_3);
x_140 = lean_array_uset(x_139, x_6, x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_expr_update_proj(x_3, x_137);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_6, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_135, 1, x_144);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_135, 0);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_135);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_3);
x_148 = lean_array_uset(x_147, x_6, x_3);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_expr_update_proj(x_3, x_145);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_6, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
case 12:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_3);
x_154 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___closed__1;
x_155 = l_unreachable_x21___rarg(x_154);
x_156 = lean_apply_1(x_155, x_4);
return x_156;
}
default: 
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_3);
lean_ctor_set(x_157, 1, x_4);
return x_157;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Std_RBNode_find___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_Replacement_apply___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Elab_Term_MutualClosure_pushMain___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_nat_sub(x_4, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_20 = l_Lean_Elab_DefViewElabHeader_inhabited;
x_21 = lean_array_get(x_20, x_2, x_19);
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_3, x_19);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_1);
x_24 = l_Lean_Meta_mkLambdaFVars___at_Lean_Elab_Term_elabFun___spec__1(x_1, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_21, 6);
lean_inc(x_27);
lean_inc(x_9);
lean_inc(x_1);
x_28 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*8);
x_32 = lean_box(0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_21, 3);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_25);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_31);
x_36 = lean_array_push(x_6, x_35);
x_5 = x_17;
x_6 = x_36;
x_13 = x_30;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
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
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_46; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_pushMain(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_get_size(x_3);
lean_inc(x_12);
x_13 = l_Nat_foldMAux___main___at_Lean_Elab_Term_MutualClosure_pushMain___spec__1(x_2, x_3, x_4, x_12, x_12, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
return x_13;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Elab_Term_MutualClosure_pushMain___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldMAux___main___at_Lean_Elab_Term_MutualClosure_pushMain___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_pushMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_MutualClosure_pushMain(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 7);
lean_inc(x_9);
lean_inc(x_7);
x_10 = l_Lean_Meta_Closure_mkForall(x_7, x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_8, 8);
lean_inc(x_11);
x_12 = l_Lean_Meta_Closure_mkLambda(x_7, x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
lean_inc(x_14);
x_20 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_15);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 1, x_16);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 2, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 3, x_18);
x_21 = lean_ctor_get(x_8, 4);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_10);
lean_ctor_set(x_22, 4, x_12);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_1);
x_23 = lean_array_push(x_3, x_22);
x_3 = x_23;
x_4 = x_6;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_pushLetRecs(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1(x_3, x_4, x_1, x_2);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_pushLetRecs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Elab_Term_MutualClosure_pushLetRecs(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getKindForLetRecs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_dec(x_7);
x_9 = l_Lean_Elab_DefKind_isTheorem(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
uint8_t l_Lean_Elab_Term_MutualClosure_getKindForLetRecs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getKindForLetRecs___spec__1(x_1, x_1, x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getKindForLetRecs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getKindForLetRecs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_getKindForLetRecs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_MutualClosure_getKindForLetRecs(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*2 + 1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*2 + 2);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*2 + 3);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
return x_9;
}
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_box(0);
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__1(x_1, x_1, x_3, x_4);
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__2(x_1, x_1, x_3, x_4);
x_7 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__3(x_1, x_1, x_3, x_4);
lean_dec(x_3);
x_8 = 0;
x_9 = l_Array_empty___closed__1;
x_10 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2 + 1, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*2 + 2, x_6);
lean_ctor_set_uint8(x_10, sizeof(void*)*2 + 3, x_7);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_6, 2);
lean_dec(x_9);
x_10 = l_Lean_NameSet_empty;
lean_ctor_set(x_6, 2, x_10);
x_11 = lean_st_ref_set(x_1, x_6, x_7);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = l_Lean_NameSet_empty;
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_ref_set(x_1, x_21, x_7);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_24 = x_22;
} else {
 lean_dec_ref(x_22);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_check(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 8);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Meta_check(x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 5);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 6);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 7);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__2___boxed), 9, 1);
lean_closure_set(x_17, 0, x_11);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 9, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabBinders___spec__2___rarg(x_13, x_14, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_1 = x_12;
x_8 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_19;
x_24 = lean_array_fset(x_16, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_9 = x_20;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtHeader(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_19;
x_24 = lean_array_fset(x_16, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_9 = x_20;
goto _start;
}
}
}
lean_object* l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
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
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_12, 2);
x_16 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_12, 2, x_17);
x_19 = l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get(x_12, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_29 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_30);
x_33 = l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_32);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 2);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 3, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_41);
lean_ctor_set(x_47, 2, x_45);
x_48 = l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_9, x_2, x_14);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 6);
x_13 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_12);
lean_ctor_set(x_10, 6, x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = x_10;
x_17 = lean_array_fset(x_9, x_2, x_16);
lean_dec(x_2);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
x_22 = lean_ctor_get(x_10, 2);
x_23 = lean_ctor_get(x_10, 3);
x_24 = lean_ctor_get(x_10, 4);
x_25 = lean_ctor_get(x_10, 5);
x_26 = lean_ctor_get(x_10, 6);
x_27 = lean_ctor_get(x_10, 7);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_28 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_26);
x_29 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_28);
lean_ctor_set(x_29, 7, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*8, x_21);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
x_32 = x_29;
x_33 = lean_array_fset(x_9, x_2, x_32);
lean_dec(x_2);
x_2 = x_31;
x_3 = x_33;
goto _start;
}
}
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_4, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 9);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 7);
lean_inc(x_19);
x_20 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_19);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_5, 8);
x_23 = lean_ctor_get(x_5, 9);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 7);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 6);
lean_dec(x_25);
x_26 = lean_ctor_get(x_5, 5);
lean_dec(x_26);
x_27 = lean_ctor_get(x_5, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_5, 3);
lean_dec(x_28);
x_29 = lean_ctor_get(x_5, 2);
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_22);
lean_ctor_set(x_5, 8, x_32);
lean_ctor_set(x_5, 7, x_20);
x_33 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_1, x_7);
lean_ctor_set(x_2, 1, x_33);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_5, 8);
lean_inc(x_34);
lean_dec(x_5);
x_35 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_34);
x_36 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_12);
lean_ctor_set(x_36, 2, x_13);
lean_ctor_set(x_36, 3, x_14);
lean_ctor_set(x_36, 4, x_15);
lean_ctor_set(x_36, 5, x_16);
lean_ctor_set(x_36, 6, x_17);
lean_ctor_set(x_36, 7, x_20);
lean_ctor_set(x_36, 8, x_35);
lean_ctor_set(x_36, 9, x_18);
lean_ctor_set(x_4, 2, x_36);
x_37 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_1, x_7);
lean_ctor_set(x_2, 1, x_37);
return x_2;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_4, 0);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_40 = lean_ctor_get(x_5, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_5, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_5, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_5, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_5, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 9);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 7);
lean_inc(x_48);
x_49 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_48);
x_50 = lean_ctor_get(x_5, 8);
lean_inc(x_50);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 x_51 = x_5;
} else {
 lean_dec_ref(x_5);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_50);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 10, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
lean_ctor_set(x_53, 2, x_42);
lean_ctor_set(x_53, 3, x_43);
lean_ctor_set(x_53, 4, x_44);
lean_ctor_set(x_53, 5, x_45);
lean_ctor_set(x_53, 6, x_46);
lean_ctor_set(x_53, 7, x_49);
lean_ctor_set(x_53, 8, x_52);
lean_ctor_set(x_53, 9, x_47);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set(x_54, 2, x_53);
x_55 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_1, x_7);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_57 = lean_ctor_get(x_4, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_4, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_59 = x_4;
} else {
 lean_dec_ref(x_4);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_5, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_5, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_5, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_5, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_5, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_5, 9);
lean_inc(x_67);
x_68 = lean_ctor_get(x_5, 7);
lean_inc(x_68);
x_69 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_68);
x_70 = lean_ctor_get(x_5, 8);
lean_inc(x_70);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 x_71 = x_5;
} else {
 lean_dec_ref(x_5);
 x_71 = lean_box(0);
}
x_72 = l_Lean_Elab_Term_MutualClosure_Replacement_apply(x_1, x_70);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 10, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set(x_73, 2, x_62);
lean_ctor_set(x_73, 3, x_63);
lean_ctor_set(x_73, 4, x_64);
lean_ctor_set(x_73, 5, x_65);
lean_ctor_set(x_73, 6, x_66);
lean_ctor_set(x_73, 7, x_69);
lean_ctor_set(x_73, 8, x_72);
lean_ctor_set(x_73, 9, x_67);
if (lean_is_scalar(x_59)) {
 x_74 = lean_alloc_ctor(0, 3, 0);
} else {
 x_74 = x_59;
}
lean_ctor_set(x_74, 0, x_57);
lean_ctor_set(x_74, 1, x_58);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_1, x_56);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l_Lean_Elab_Term_MutualClosure_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_3);
x_13 = x_3;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__3(x_14, x_13);
x_16 = x_15;
x_17 = l_List_redLength___main___rarg(x_5);
x_18 = lean_mk_empty_array_with_capacity(x_17);
lean_dec(x_17);
lean_inc(x_5);
x_19 = l_List_toArrayAux___main___rarg(x_5, x_18);
x_20 = x_19;
x_21 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__1(x_14, x_20);
x_22 = x_21;
x_23 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_16, x_16, x_14, x_22);
x_24 = lean_st_ref_get(x_9, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
x_28 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkFreeVarMap(x_27, x_1, x_16, x_23, x_5);
lean_dec(x_23);
lean_dec(x_16);
x_29 = l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___rarg(x_9, x_10, x_11, x_26);
x_30 = lean_ctor_get(x_8, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_8, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
x_35 = 1;
lean_ctor_set_uint8(x_30, 7, x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_38 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_28);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = x_4;
x_42 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4___boxed), 9, 2);
lean_closure_set(x_42, 0, x_14);
lean_closure_set(x_42, 1, x_41);
x_43 = x_42;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = lean_apply_7(x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = x_2;
x_48 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5___boxed), 9, 2);
lean_closure_set(x_48, 0, x_14);
lean_closure_set(x_48, 1, x_47);
x_49 = x_48;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = lean_apply_7(x_49, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
x_57 = l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns(x_56, x_1, x_51, x_3);
lean_dec(x_3);
lean_inc(x_54);
x_58 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs___spec__1(x_57, x_54);
x_59 = x_45;
x_60 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7(x_58, x_14, x_59);
x_61 = x_60;
x_62 = x_51;
x_63 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8(x_58, x_14, x_62);
x_64 = x_63;
x_65 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_58, x_54);
lean_dec(x_58);
x_66 = l_Lean_Elab_Term_MutualClosure_getKindForLetRecs(x_64);
x_67 = l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs(x_64);
x_68 = l_Array_empty___closed__1;
x_69 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1(x_66, x_67, x_68, x_65);
lean_dec(x_67);
x_70 = l_Lean_Elab_Term_MutualClosure_pushMain(x_69, x_1, x_64, x_61, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_61);
lean_dec(x_64);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
return x_70;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
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
lean_dec(x_45);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_50);
if (x_79 == 0)
{
return x_50;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_50, 0);
x_81 = lean_ctor_get(x_50, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_50);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_44);
if (x_83 == 0)
{
return x_44;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_44, 0);
x_85 = lean_ctor_get(x_44, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_44);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_38);
if (x_87 == 0)
{
return x_38;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_38, 0);
x_89 = lean_ctor_get(x_38, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_38);
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
lean_dec(x_8);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_36);
if (x_91 == 0)
{
return x_36;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_36, 0);
x_93 = lean_ctor_get(x_36, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_36);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_95 = lean_ctor_get_uint8(x_30, 0);
x_96 = lean_ctor_get_uint8(x_30, 1);
x_97 = lean_ctor_get_uint8(x_30, 2);
x_98 = lean_ctor_get_uint8(x_30, 3);
x_99 = lean_ctor_get_uint8(x_30, 4);
x_100 = lean_ctor_get_uint8(x_30, 5);
x_101 = lean_ctor_get_uint8(x_30, 6);
lean_dec(x_30);
x_102 = 1;
x_103 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_103, 0, x_95);
lean_ctor_set_uint8(x_103, 1, x_96);
lean_ctor_set_uint8(x_103, 2, x_97);
lean_ctor_set_uint8(x_103, 3, x_98);
lean_ctor_set_uint8(x_103, 4, x_99);
lean_ctor_set_uint8(x_103, 5, x_100);
lean_ctor_set_uint8(x_103, 6, x_101);
lean_ctor_set_uint8(x_103, 7, x_102);
lean_ctor_set(x_8, 0, x_103);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_104 = l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_106 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_105);
lean_dec(x_28);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = x_4;
x_110 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4___boxed), 9, 2);
lean_closure_set(x_110, 0, x_14);
lean_closure_set(x_110, 1, x_109);
x_111 = x_110;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_112 = lean_apply_7(x_111, x_6, x_7, x_8, x_9, x_10, x_11, x_108);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = x_2;
x_116 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5___boxed), 9, 2);
lean_closure_set(x_116, 0, x_14);
lean_closure_set(x_116, 1, x_115);
x_117 = x_116;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_118 = lean_apply_7(x_117, x_6, x_7, x_8, x_9, x_10, x_11, x_114);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(x_107, x_6, x_7, x_8, x_9, x_10, x_11, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_box(0);
x_125 = l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns(x_124, x_1, x_119, x_3);
lean_dec(x_3);
lean_inc(x_122);
x_126 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs___spec__1(x_125, x_122);
x_127 = x_113;
x_128 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7(x_126, x_14, x_127);
x_129 = x_128;
x_130 = x_119;
x_131 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8(x_126, x_14, x_130);
x_132 = x_131;
x_133 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_126, x_122);
lean_dec(x_126);
x_134 = l_Lean_Elab_Term_MutualClosure_getKindForLetRecs(x_132);
x_135 = l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs(x_132);
x_136 = l_Array_empty___closed__1;
x_137 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1(x_134, x_135, x_136, x_133);
lean_dec(x_135);
x_138 = l_Lean_Elab_Term_MutualClosure_pushMain(x_137, x_1, x_132, x_129, x_6, x_7, x_8, x_9, x_10, x_11, x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_129);
lean_dec(x_132);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_138, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_145 = x_138;
} else {
 lean_dec_ref(x_138);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_113);
lean_dec(x_107);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_147 = lean_ctor_get(x_118, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_118, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_149 = x_118;
} else {
 lean_dec_ref(x_118);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_107);
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = lean_ctor_get(x_112, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_112, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_153 = x_112;
} else {
 lean_dec_ref(x_112);
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
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_8);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_ctor_get(x_106, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_106, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_157 = x_106;
} else {
 lean_dec_ref(x_106);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_8);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_104, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_104, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_161 = x_104;
} else {
 lean_dec_ref(x_104);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_163 = lean_ctor_get(x_8, 1);
x_164 = lean_ctor_get(x_8, 2);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_8);
x_165 = lean_ctor_get_uint8(x_30, 0);
x_166 = lean_ctor_get_uint8(x_30, 1);
x_167 = lean_ctor_get_uint8(x_30, 2);
x_168 = lean_ctor_get_uint8(x_30, 3);
x_169 = lean_ctor_get_uint8(x_30, 4);
x_170 = lean_ctor_get_uint8(x_30, 5);
x_171 = lean_ctor_get_uint8(x_30, 6);
if (lean_is_exclusive(x_30)) {
 x_172 = x_30;
} else {
 lean_dec_ref(x_30);
 x_172 = lean_box(0);
}
x_173 = 1;
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 0, 8);
} else {
 x_174 = x_172;
}
lean_ctor_set_uint8(x_174, 0, x_165);
lean_ctor_set_uint8(x_174, 1, x_166);
lean_ctor_set_uint8(x_174, 2, x_167);
lean_ctor_set_uint8(x_174, 3, x_168);
lean_ctor_set_uint8(x_174, 4, x_169);
lean_ctor_set_uint8(x_174, 5, x_170);
lean_ctor_set_uint8(x_174, 6, x_171);
lean_ctor_set_uint8(x_174, 7, x_173);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_163);
lean_ctor_set(x_175, 2, x_164);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_175);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_176 = l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3(x_5, x_6, x_7, x_175, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_175);
lean_inc(x_7);
lean_inc(x_6);
x_178 = l_List_mapM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkLetRecClosures___spec__2(x_28, x_5, x_6, x_7, x_175, x_9, x_10, x_11, x_177);
lean_dec(x_28);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = x_4;
x_182 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4___boxed), 9, 2);
lean_closure_set(x_182, 0, x_14);
lean_closure_set(x_182, 1, x_181);
x_183 = x_182;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_175);
lean_inc(x_7);
lean_inc(x_6);
x_184 = lean_apply_7(x_183, x_6, x_7, x_175, x_9, x_10, x_11, x_180);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = x_2;
x_188 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5___boxed), 9, 2);
lean_closure_set(x_188, 0, x_14);
lean_closure_set(x_188, 1, x_187);
x_189 = x_188;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_175);
lean_inc(x_7);
lean_inc(x_6);
x_190 = lean_apply_7(x_189, x_6, x_7, x_175, x_9, x_10, x_11, x_186);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(x_179, x_6, x_7, x_175, x_9, x_10, x_11, x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_box(0);
x_197 = l_Lean_Elab_Term_MutualClosure_insertReplacementForMainFns(x_196, x_1, x_191, x_3);
lean_dec(x_3);
lean_inc(x_194);
x_198 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_insertReplacementForLetRecs___spec__1(x_197, x_194);
x_199 = x_185;
x_200 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7(x_198, x_14, x_199);
x_201 = x_200;
x_202 = x_191;
x_203 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8(x_198, x_14, x_202);
x_204 = x_203;
x_205 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_198, x_194);
lean_dec(x_198);
x_206 = l_Lean_Elab_Term_MutualClosure_getKindForLetRecs(x_204);
x_207 = l_Lean_Elab_Term_MutualClosure_getModifiersForLetRecs(x_204);
x_208 = l_Array_empty___closed__1;
x_209 = l_List_foldl___main___at_Lean_Elab_Term_MutualClosure_pushLetRecs___spec__1(x_206, x_207, x_208, x_205);
lean_dec(x_207);
x_210 = l_Lean_Elab_Term_MutualClosure_pushMain(x_209, x_1, x_204, x_201, x_6, x_7, x_175, x_9, x_10, x_11, x_195);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_201);
lean_dec(x_204);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_210, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_217 = x_210;
} else {
 lean_dec_ref(x_210);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_185);
lean_dec(x_179);
lean_dec(x_175);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_219 = lean_ctor_get(x_190, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_190, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_221 = x_190;
} else {
 lean_dec_ref(x_190);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_179);
lean_dec(x_175);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_184, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_184, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_225 = x_184;
} else {
 lean_dec_ref(x_184);
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
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_175);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_178, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_178, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_229 = x_178;
} else {
 lean_dec_ref(x_178);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_175);
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = lean_ctor_get(x_176, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_176, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_233 = x_176;
} else {
 lean_dec_ref(x_176);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_resetZetaFVarIds___at_Lean_Elab_Term_MutualClosure_main___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___main___at_Lean_Elab_Term_MutualClosure_main___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___main___at_Lean_Elab_Term_MutualClosure_main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__8(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at_Lean_Elab_Term_MutualClosure_main___spec__9(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getAllUserLevelNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getAllUserLevelNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getAllUserLevelNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_instantiateMVarsAtLetRecToLift(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMutualDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Elab_Term_MutualClosure_main(x_7, x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Elab_levelMVarToParamPreDecls(x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Elab_instantiateMVarsAtPreDecls(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
x_24 = l_Lean_Elab_fixLevelParams(x_22, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_addPreDefinitions(x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMutualDef___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_19);
x_24 = x_15;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4___boxed), 9, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_24);
x_27 = x_26;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = lean_apply_7(x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = x_1;
x_32 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5___boxed), 9, 2);
lean_closure_set(x_32, 0, x_25);
lean_closure_set(x_32, 1, x_31);
x_33 = x_32;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = lean_apply_7(x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getLetRecsToLift___rarg(x_8, x_9, x_10, x_11, x_12, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1(x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_7);
lean_inc_n(x_41, 2);
x_43 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1(x_6, x_41, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem(x_2);
lean_inc(x_41);
lean_inc(x_29);
lean_inc(x_35);
x_46 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMutualDef___lambda__1), 14, 6);
lean_closure_set(x_46, 0, x_35);
lean_closure_set(x_46, 1, x_6);
lean_closure_set(x_46, 2, x_29);
lean_closure_set(x_46, 3, x_41);
lean_closure_set(x_46, 4, x_3);
lean_closure_set(x_46, 5, x_4);
if (x_45 == 0)
{
uint8_t x_47; lean_object* x_48; 
x_47 = 1;
x_48 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg(x_5, x_35, x_29, x_41, x_47, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_29);
lean_dec(x_35);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg(x_5, x_35, x_29, x_41, x_17, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_29);
lean_dec(x_35);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_29);
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
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
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
lean_dec(x_29);
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
x_54 = !lean_is_exclusive(x_34);
if (x_54 == 0)
{
return x_34;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
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
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_28);
if (x_58 == 0)
{
return x_28;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_28, 0);
x_60 = lean_ctor_get(x_28, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_28);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
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
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_19, 1);
lean_inc(x_62);
lean_dec(x_19);
x_63 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isExample(x_2);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = x_15;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__4___boxed), 9, 2);
lean_closure_set(x_66, 0, x_65);
lean_closure_set(x_66, 1, x_64);
x_67 = x_66;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_68 = lean_apply_7(x_67, x_7, x_8, x_9, x_10, x_11, x_12, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = x_1;
x_72 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_MutualClosure_main___spec__5___boxed), 9, 2);
lean_closure_set(x_72, 0, x_65);
lean_closure_set(x_72, 1, x_71);
x_73 = x_72;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_74 = lean_apply_7(x_73, x_7, x_8, x_9, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Term_getLetRecsToLift___rarg(x_8, x_9, x_10, x_11, x_12, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1(x_78, x_7, x_8, x_9, x_10, x_11, x_12, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_7);
lean_inc_n(x_81, 2);
x_83 = l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1(x_6, x_81, x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_isTheorem(x_2);
lean_inc(x_81);
lean_inc(x_69);
lean_inc(x_75);
x_86 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMutualDef___lambda__1), 14, 6);
lean_closure_set(x_86, 0, x_75);
lean_closure_set(x_86, 1, x_6);
lean_closure_set(x_86, 2, x_69);
lean_closure_set(x_86, 3, x_81);
lean_closure_set(x_86, 4, x_3);
lean_closure_set(x_86, 5, x_4);
if (x_85 == 0)
{
uint8_t x_87; lean_object* x_88; 
x_87 = 1;
x_88 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg(x_5, x_75, x_69, x_81, x_87, x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_84);
lean_dec(x_69);
lean_dec(x_75);
return x_88;
}
else
{
lean_object* x_89; 
x_89 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withUsedWhen___rarg(x_5, x_75, x_69, x_81, x_17, x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_84);
lean_dec(x_69);
lean_dec(x_75);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_81);
lean_dec(x_75);
lean_dec(x_69);
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
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_92 = x_83;
} else {
 lean_dec_ref(x_83);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_69);
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
x_94 = lean_ctor_get(x_74, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_74, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_96 = x_74;
} else {
 lean_dec_ref(x_74);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
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
lean_dec(x_1);
x_98 = lean_ctor_get(x_68, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_68, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_100 = x_68;
} else {
 lean_dec_ref(x_68);
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
else
{
lean_object* x_102; 
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
lean_dec(x_3);
lean_dec(x_1);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_18);
lean_ctor_set(x_102, 1, x_62);
return x_102;
}
}
}
else
{
uint8_t x_103; 
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
lean_dec(x_3);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_19);
if (x_103 == 0)
{
return x_19;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_19, 0);
x_105 = lean_ctor_get(x_19, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_19);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
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
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_14);
if (x_107 == 0)
{
return x_14;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_14, 0);
x_109 = lean_ctor_get(x_14, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_14);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabMutualDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Elab_Term_getLevelNames(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabHeaders(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getAllUserLevelNames(x_14);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabMutualDef___lambda__2___boxed), 13, 5);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_11);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_1);
x_18 = l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_withFunLocalDecls___rarg(x_14, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___main___at_Lean_Elab_Term_elabMutualDef___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabMutualDef___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_elabMutualDef___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_addMessageContextPartial___at_Lean_Elab_Command_Lean_AddMessageContext___spec__1(x_1, x_2, x_3, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Command_Lean_AddErrorMessageContext___spec__1(x_11, x_8, x_2, x_3, x_12);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_getNumArgs(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__1(x_2, x_8, x_12, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__1(x_2, x_14, x_15, x_4, x_5, x_6);
return x_16;
}
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_isAttribute(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = l_Lean_Elab_elabAttr___rarg___lambda__3___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_elabAttr___rarg___lambda__3___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(x_15, x_3, x_4, x_8);
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
x_22 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__2(x_1, x_2, x_21, x_3, x_4, x_8);
lean_dec(x_3);
return x_22;
}
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_isIdOrAtom_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_replaceRef(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 6);
lean_dec(x_13);
lean_ctor_set(x_2, 6, x_11);
x_14 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_15 = l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(x_14, x_2, x_3, x_10);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
x_24 = lean_ctor_get(x_2, 4);
x_25 = lean_ctor_get(x_2, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_11);
x_27 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_28 = l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(x_27, x_26, x_3, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_6);
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_box(0);
x_35 = lean_name_mk_string(x_34, x_33);
x_36 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__3(x_1, x_35, x_2, x_3, x_4);
return x_36;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutualDef___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_3 < x_2;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_1, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4(x_10, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_push(x_4, x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Syntax_getSepArgs(x_1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = l_Array_empty___closed__1;
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutualDef___spec__6(x_5, x_7, x_8, x_9, x_2, x_3, x_4);
lean_dec(x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
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
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at_Lean_Elab_Command_elabMutualDef___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(x_6, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(x_2, x_3, x_4, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 2);
x_16 = lean_ctor_get(x_3, 3);
x_17 = lean_ctor_get(x_3, 4);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
lean_ctor_set(x_19, 6, x_9);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(x_2, x_19, x_4, x_8);
return x_20;
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = l_Lean_Syntax_isNone(x_1);
x_11 = l_Lean_Syntax_isNone(x_2);
x_12 = l_Lean_Syntax_isNone(x_3);
if (x_10 == 0)
{
if (x_11 == 0)
{
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_13 = 1;
x_14 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 1, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 2, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 1;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 3, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
else
{
if (x_12 == 0)
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 1;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 2, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 3, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 1;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_6);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 1, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 2, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 3, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
else
{
if (x_11 == 0)
{
if (x_12 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
x_29 = 1;
x_30 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 1, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 2, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2 + 3, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
else
{
uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 0;
x_33 = 1;
x_34 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 2, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 3, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
else
{
if (x_12 == 0)
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = 0;
x_37 = 1;
x_38 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 1, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 2, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 1, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 2, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 3, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
}
}
}
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Syntax_getOptional_x3f(x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Array_empty___closed__1;
x_12 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_6, x_11, x_7, x_8, x_9);
lean_dec(x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_7);
x_14 = l_Lean_Elab_elabDeclAttrs___at_Lean_Elab_Command_elabMutualDef___spec__2(x_13, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_6, x_15, x_7, x_8, x_16);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_4);
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
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Syntax_getOptional_x3f(x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2(x_1, x_2, x_3, x_6, x_4, x_11, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_13);
x_14 = l_Lean_Syntax_getKind(x_13);
x_15 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
x_16 = lean_name_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
x_18 = lean_name_eq(x_14, x_17);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
x_19 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
x_20 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg(x_13, x_19, x_7, x_8, x_9);
lean_dec(x_13);
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
uint8_t x_25; lean_object* x_26; 
lean_dec(x_13);
x_25 = 1;
x_26 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2(x_1, x_2, x_3, x_6, x_4, x_25, x_7, x_8, x_9);
return x_26;
}
}
else
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_13);
x_27 = 2;
x_28 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2(x_1, x_2, x_3, x_6, x_4, x_27, x_7, x_8, x_9);
return x_28;
}
}
}
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getOptional_x3f(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3(x_12, x_16, x_14, x_8, x_10, x_18, x_2, x_3, x_4);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_14);
lean_dec(x_16);
lean_dec(x_12);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = l_Lean_Syntax_getArg(x_21, x_7);
if (lean_obj_tag(x_22) == 2)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_string_utf8_byte_size(x_23);
x_25 = lean_nat_sub(x_24, x_9);
lean_dec(x_24);
x_26 = lean_string_utf8_extract(x_23, x_5, x_25);
lean_dec(x_25);
lean_dec(x_23);
lean_ctor_set(x_17, 0, x_26);
x_27 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3(x_12, x_16, x_14, x_8, x_10, x_17, x_2, x_3, x_4);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_14);
lean_dec(x_16);
lean_dec(x_12);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_free_object(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_29 = l_Lean_Elab_elabModifiers___rarg___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg(x_21, x_32, x_2, x_3, x_4);
lean_dec(x_21);
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
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
lean_dec(x_17);
x_39 = l_Lean_Syntax_getArg(x_38, x_7);
if (lean_obj_tag(x_39) == 2)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_string_utf8_byte_size(x_40);
x_42 = lean_nat_sub(x_41, x_9);
lean_dec(x_41);
x_43 = lean_string_utf8_extract(x_40, x_5, x_42);
lean_dec(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3(x_12, x_16, x_14, x_8, x_10, x_44, x_2, x_3, x_4);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_14);
lean_dec(x_16);
lean_dec(x_12);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_39);
x_47 = l_Lean_Elab_elabModifiers___rarg___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__5;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg(x_38, x_50, x_2, x_3, x_4);
lean_dec(x_38);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Command_elabMutualDef___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_2, x_1, x_11);
x_13 = x_10;
x_14 = l_Lean_Syntax_getArg(x_13, x_11);
lean_inc(x_3);
x_15 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_14, x_3, x_4, x_5);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
lean_inc(x_3);
x_20 = l_Lean_Elab_Command_mkDefView(x_16, x_19, x_3, x_4, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_add(x_1, x_18);
x_24 = x_21;
x_25 = lean_array_fset(x_12, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_5 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabMutualDef___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_resetMessageLog(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Term_elabMutualDef(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_elabMutualDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = x_1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Command_elabMutualDef___spec__8___boxed), 5, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = x_7;
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_apply_3(x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_st_ref_get(x_3, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_Command_4__getVarDecls(x_14);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutualDef___lambda__1), 9, 1);
lean_closure_set(x_17, 0, x_10);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Command_liftTermElabM___rarg(x_12, x_18, x_2, x_3, x_15);
lean_dec(x_3);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_Elab_Command_elabMutualDef___spec__5___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabAttr___at_Lean_Elab_Command_elabMutualDef___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutualDef___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabMutualDef___spec__6(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabAttrs___at_Lean_Elab_Command_elabMutualDef___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at_Lean_Elab_Command_elabMutualDef___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabDeclAttrs___at_Lean_Elab_Command_elabMutualDef___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabMutualDef___spec__7___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabModifiers___at_Lean_Elab_Command_elabMutualDef___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Command_elabMutualDef___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at_Lean_Elab_Command_elabMutualDef___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Closure(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_DefView(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_MutualDef(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DefView(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_DefViewElabHeader_inhabited___closed__1 = _init_l_Lean_Elab_DefViewElabHeader_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_DefViewElabHeader_inhabited___closed__1);
l_Lean_Elab_DefViewElabHeader_inhabited = _init_l_Lean_Elab_DefViewElabHeader_inhabited();
lean_mark_persistent(l_Lean_Elab_DefViewElabHeader_inhabited);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__1___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___lambda__2___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkModifiers___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___lambda__1___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkKinds___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__4 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__4);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__2___closed__5);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__3___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__4___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__5___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__6___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___lambda__7___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_check___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_registerFailedToInferDefTypeInfo___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_declValToTerm___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_elabFunValues___spec__1___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_removeUnusedVars___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_getFunName___closed__3);
l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__1 = _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__1();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__1);
l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__2 = _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__2();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__2);
l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__3 = _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__3();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__3);
l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__4 = _init_l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__4();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_checkLetRecsToLiftTypes___spec__1___closed__4);
l_Lean_Elab_Term_MutualClosure_FixPoint_State_usedFVarsMap___default = _init_l_Lean_Elab_Term_MutualClosure_FixPoint_State_usedFVarsMap___default();
lean_mark_persistent(l_Lean_Elab_Term_MutualClosure_FixPoint_State_usedFVarsMap___default);
l_Lean_Elab_Term_MutualClosure_FixPoint_State_modified___default = _init_l_Lean_Elab_Term_MutualClosure_FixPoint_State_modified___default();
l_Lean_Elab_Term_MutualClosure_ClosureState_newLocalDecls___default = _init_l_Lean_Elab_Term_MutualClosure_ClosureState_newLocalDecls___default();
lean_mark_persistent(l_Lean_Elab_Term_MutualClosure_ClosureState_newLocalDecls___default);
l_Lean_Elab_Term_MutualClosure_ClosureState_localDecls___default = _init_l_Lean_Elab_Term_MutualClosure_ClosureState_localDecls___default();
lean_mark_persistent(l_Lean_Elab_Term_MutualClosure_ClosureState_localDecls___default);
l_Lean_Elab_Term_MutualClosure_ClosureState_newLetDecls___default = _init_l_Lean_Elab_Term_MutualClosure_ClosureState_newLetDecls___default();
lean_mark_persistent(l_Lean_Elab_Term_MutualClosure_ClosureState_newLetDecls___default);
l_Lean_Elab_Term_MutualClosure_ClosureState_exprArgs___default = _init_l_Lean_Elab_Term_MutualClosure_ClosureState_exprArgs___default();
lean_mark_persistent(l_Lean_Elab_Term_MutualClosure_ClosureState_exprArgs___default);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__1 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__1);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__2 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__2);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__3 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__3);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__4 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__4);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__5 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__5);
l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__6 = _init_l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_MutualDef_0__Lean_Elab_Term_MutualClosure_mkClosureForAux___closed__6);
l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at_Lean_Elab_Term_MutualClosure_Replacement_apply___spec__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
