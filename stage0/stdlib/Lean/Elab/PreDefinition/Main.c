// Lean compiler output
// Module: Lean.Elab.PreDefinition.Main
// Imports: Init Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Structural Lean.Elab.PreDefinition.WF
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
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_963____closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__14(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___lambda__1(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafeRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_List_map___at_Lean_Elab_addPreDefinitions___spec__3(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__1;
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__23(lean_object*);
extern lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef_match__1(lean_object*);
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__6(size_t, size_t, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__10(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8(lean_object*, size_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__3;
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(lean_object*, size_t, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Std_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1;
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__1;
lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__24(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__2;
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__2;
lean_object* l_List_map___at_Lean_Elab_addPreDefinitions___spec__7(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_collectMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__4(lean_object*, size_t, size_t, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs(lean_object*);
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___boxed(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addPreDefinitions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
extern lean_object* l_Option_get_x21___rarg___closed__4;
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__15(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__2;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__1;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___boxed__const__1;
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__2;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__4;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(lean_object*, size_t, size_t);
extern lean_object* l_Lean_Expr_FoldConstsImpl_initCache;
lean_object* l_Lean_Elab_WFRecursion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___lambda__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
extern lean_object* l_Lean_CollectMVars_instInhabitedState___closed__1;
extern lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1;
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__1;
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__19(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
lean_object* l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inhabitant for ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_13);
x_14 = l_Lean_Elab_mkInhabitantFor(x_13, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_39 = lean_st_ref_get(x_11, x_16);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_17 = x_44;
x_18 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
lean_inc(x_3);
x_46 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_17 = x_49;
x_18 = x_48;
goto block_38;
}
block_38:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_2);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_21);
x_23 = 0;
x_24 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_22, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_inc(x_13);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_13);
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_KernelException_toMessageData___closed__15;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_3, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_13);
lean_ctor_set(x_35, 3, x_2);
lean_ctor_set(x_35, 4, x_15);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_34);
x_36 = 0;
x_37 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_35, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
return x_37;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_14);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("processing ");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_25; lean_object* x_26; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_st_ref_get(x_7, x_8);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 3);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = 0;
x_25 = x_42;
x_26 = x_41;
goto block_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
x_44 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_963____closed__2;
x_45 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_25 = x_48;
x_26 = x_47;
goto block_36;
}
block_24:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_963____closed__2;
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___boxed), 12, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_Meta_forallTelescope___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryPureCoe_x3f___spec__3___rarg(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
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
block_36:
{
if (x_25 == 0)
{
x_9 = x_26;
goto block_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_KernelException_toMessageData___closed__15;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_963____closed__2;
x_34 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_33, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_9 = x_35;
goto block_24;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_9(x_19, lean_box(0), x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
else
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = 1;
x_23 = x_2 + x_22;
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1(x_3, x_4, x_5, x_6, x_1, x_7, x_8, x_23, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_24;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = x_8 < x_7;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_9(x_19, lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_9);
x_21 = lean_array_uget(x_6, x_8);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2), 8, 1);
lean_closure_set(x_23, 0, x_21);
x_24 = lean_box_usize(x_8);
x_25 = lean_box_usize(x_7);
x_26 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__3___boxed), 16, 8);
lean_closure_set(x_26, 0, x_5);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_3);
lean_closure_set(x_26, 5, x_4);
lean_closure_set(x_26, 6, x_6);
lean_closure_set(x_26, 7, x_25);
x_27 = lean_apply_11(x_22, lean_box(0), lean_box(0), x_23, x_26, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_27;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__1;
x_13 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__2;
x_14 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__3;
x_15 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
x_16 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_17 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1(x_12, x_13, x_14, x_15, x_16, x_1, x_10, x_11, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_addAndCompileUnsafeRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__3(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_name_eq(x_4, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = 8192;
x_5 = l_Lean_Expr_FindImpl_initCache;
x_6 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_2, x_4, x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = 0;
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = x_5 + x_11;
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(lean_object* x_1) {
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
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(x_5);
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
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = x_5 + x_11;
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = x_3 + x_9;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(x_3, x_1);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___rarg___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
uint8_t l_Std_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__15(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__15(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__14(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__13(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__16(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_push___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_5, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_11 = 1;
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_11);
x_13 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_6, x_1, x_12);
lean_ctor_set(x_2, 2, x_13);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_17, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_24 = 1;
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
x_26 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_18, x_1, x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_19);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_1(x_2, x_9);
x_11 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_5, x_1, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_3, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_18 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(x_16, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_apply_1(x_2, x_22);
x_24 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__11(x_16, x_1, x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 2, x_24);
lean_ctor_set(x_25, 3, x_17);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_7, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_1);
x_13 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(x_1, x_7, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_7, x_14);
lean_dec(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_2);
x_19 = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(x_2, x_18, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_3 = x_8;
x_4 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
x_22 = lean_ctor_get_uint8(x_10, sizeof(void*)*2);
lean_dec(x_10);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_11);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_3 = x_8;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
lean_inc(x_2);
x_26 = l___private_Lean_Util_SCC_0__Lean_SCC_updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__17(x_2, x_11, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_3 = x_8;
x_4 = x_27;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___closed__1;
x_4 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_4, 3, x_9);
lean_ctor_set(x_4, 0, x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___lambda__1), 1, 0);
lean_inc(x_20);
x_23 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_20, x_22, x_4);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
lean_inc(x_20);
lean_ctor_set(x_2, 1, x_3);
x_27 = lean_name_eq(x_1, x_20);
lean_dec(x_20);
if (x_27 == 0)
{
lean_free_object(x_23);
{
lean_object* _tmp_1 = x_21;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_25;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 3);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_25, 3, x_32);
lean_ctor_set(x_25, 0, x_21);
x_33 = lean_box(0);
lean_ctor_set(x_23, 0, x_33);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_25, 1);
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
x_39 = lean_box(0);
lean_ctor_set(x_23, 1, x_38);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_dec(x_23);
lean_inc(x_20);
lean_ctor_set(x_2, 1, x_3);
x_41 = lean_name_eq(x_1, x_20);
lean_dec(x_20);
if (x_41 == 0)
{
{
lean_object* _tmp_1 = x_21;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_40;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_40, 3);
lean_inc(x_45);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_46 = x_40;
} else {
 lean_dec_ref(x_40);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_45);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 4, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_53 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_resetOnStack___rarg___lambda__1), 1, 0);
lean_inc(x_51);
x_54 = l___private_Lean_Util_SCC_0__Lean_SCC_modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__18(x_51, x_53, x_4);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
lean_inc(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_3);
x_58 = lean_name_eq(x_1, x_51);
lean_dec(x_51);
if (x_58 == 0)
{
lean_dec(x_56);
x_2 = x_52;
x_3 = x_57;
x_4 = x_55;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 3);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 4, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_60);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_56;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(x_1, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_1);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_1, x_1);
if (x_9 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_10; 
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(x_5, x_2, x_3, x_4);
if (x_10 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; 
lean_inc(x_2);
x_4 = l___private_Lean_Util_SCC_0__Lean_SCC_push___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__10(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_44 = lean_array_get_size(x_1);
x_45 = lean_usize_of_nat(x_44);
x_46 = 0;
x_47 = l_Array_findSomeM_x3f___rarg___closed__1;
x_48 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(x_2, x_47, x_1, x_45, x_46, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___boxed__const__1;
x_52 = lean_box_usize(x_45);
lean_inc(x_1);
x_53 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___lambda__1___boxed), 6, 4);
lean_closure_set(x_53, 0, x_44);
lean_closure_set(x_53, 1, x_1);
lean_closure_set(x_53, 2, x_51);
lean_closure_set(x_53, 3, x_52);
x_54 = 8192;
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = l_Lean_Elab_instInhabitedPreDefinition;
x_56 = l_Option_get_x21___rarg___closed__4;
x_57 = lean_panic_fn(x_55, x_56);
x_58 = lean_ctor_get(x_57, 4);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Expr_FoldConstsImpl_initCache;
x_60 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_53, x_54, x_58, x_50, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_6 = x_61;
goto block_43;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_49, 0);
lean_inc(x_62);
lean_dec(x_49);
x_63 = lean_ctor_get(x_62, 4);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_Expr_FoldConstsImpl_initCache;
x_65 = l_Lean_Expr_FoldConstsImpl_fold_visit___rarg(x_53, x_54, x_63, x_50, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_6 = x_66;
goto block_43;
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_7 = l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__19(x_1, x_2, x_6, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(x_2, x_13);
lean_dec(x_2);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_9, 0, x_24);
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_9, 1);
x_30 = lean_ctor_get(x_9, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_2);
x_34 = lean_box(0);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
else
{
lean_object* x_35; 
lean_free_object(x_9);
x_35 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(x_2, x_29);
lean_dec(x_2);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_dec(x_9);
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_ctor_get(x_21, 0);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_nat_dec_eq(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(x_2, x_36);
lean_dec(x_2);
return x_42;
}
}
}
}
}
}
}
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_6, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_1);
x_12 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9(x_1, x_6, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_6);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_2 = x_7;
x_3 = x_15;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__2;
x_4 = l_List_forM___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__24(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_reverse___rarg(x_6);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_findSomeM_x3f___rarg___closed__1;
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(x_10, x_14, x_1, x_12, x_13, x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = x_3 + x_17;
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = l_Lean_Elab_instInhabitedPreDefinition;
x_20 = l_Option_get_x21___rarg___closed__4;
x_21 = lean_panic_fn(x_19, x_20);
x_22 = x_21;
x_23 = lean_array_uset(x_9, x_3, x_22);
x_3 = x_18;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = x_25;
x_27 = lean_array_uset(x_9, x_3, x_26);
x_3 = x_18;
x_4 = x_27;
goto _start;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = l_List_redLength___rarg(x_10);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
x_13 = l_List_toArrayAux___rarg(x_10, x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = x_13;
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(x_1, x_15, x_16, x_17);
x_19 = x_18;
x_20 = 1;
x_21 = x_3 + x_20;
x_22 = x_19;
x_23 = lean_array_uset(x_9, x_3, x_22);
x_3 = x_21;
x_4 = x_23;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_2 = lean_array_to_list(lean_box(0), x_1);
x_3 = l_List_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__2(x_2);
lean_inc(x_1);
x_4 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5(x_1, x_3);
x_5 = l_List_redLength___rarg(x_4);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = l_List_toArrayAux___rarg(x_4, x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = x_7;
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(x_1, x_9, x_10, x_11);
lean_dec(x_1);
x_13 = x_12;
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__4(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_SCC_0__Lean_SCC_getDataOf___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__6(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__12(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC_add___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__21(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_SCC_0__Lean_SCC_addSCC___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__20(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___lambda__1(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__25(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__26(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_collectMVars(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_collectMVars(x_11, x_2, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_CollectMVars_instInhabitedState___closed__1;
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
x_13 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_collectMVarsAtPreDef(x_1, x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_5, x_14);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_getMVarsAtPreDef(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_12, 0, x_17);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("body");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_963____closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_44 = lean_st_ref_get(x_10, x_11);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = 0;
x_15 = x_49;
x_16 = x_48;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__2;
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_15 = x_55;
x_16 = x_54;
goto block_43;
}
block_43:
{
if (x_15 == 0)
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_dec(x_14);
x_17 = 1;
x_18 = x_3 + x_17;
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_11 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; size_t x_40; lean_object* x_41; 
x_21 = lean_ctor_get(x_14, 2);
lean_inc(x_21);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_KernelException_toMessageData___closed__15;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_14, 3);
lean_inc(x_27);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_0__Lean_Elab_Structural_elimRecursion___lambda__2___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_ctor_get(x_14, 4);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
x_36 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__2;
x_37 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_36, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = 1;
x_40 = x_3 + x_39;
x_41 = lean_box(0);
x_3 = x_40;
x_4 = x_41;
x_11 = x_38;
goto _start;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
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
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_ensureNoUnassignedMVarsAtPreDef(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = 1;
x_18 = x_3 + x_17;
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_List_map___at_Lean_Elab_addPreDefinitions___spec__3(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = l_Lean_mkConst(x_6, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_List_map___at_Lean_Elab_addPreDefinitions___spec__3(x_5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_mkConst(x_13, x_14);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_List_map___at_Lean_Elab_addPreDefinitions___spec__3(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 2);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
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
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*2 + 3);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_List_map___at_Lean_Elab_addPreDefinitions___spec__7(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Elab_addPreDefinitions___spec__7(x_5);
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
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Elab_addPreDefinitions___spec__7(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fail to show termination for");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nwith errors\n");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_array_to_list(lean_box(0), x_1);
x_4 = l_List_map___at_Lean_Elab_addPreDefinitions___spec__3(x_3);
x_5 = l_Lean_MessageData_ofList___closed__3;
x_6 = l_Lean_MessageData_joinSep(x_4, x_5);
lean_dec(x_4);
x_7 = l_Lean_indentD(x_6);
x_8 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_13 = l_Lean_KernelException_toMessageData___closed__15;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Structural_structuralRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__1(x_12, x_4, x_5, x_6, x_7, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_18, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_Elab_WFRecursion___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = l_Lean_MessageData_ofList___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_30, 1, x_37);
lean_ctor_set(x_30, 0, x_26);
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Lean_MessageData_ofList___closed__3;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_28, 0, x_43);
return x_28;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
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
x_48 = l_Lean_MessageData_ofList___closed__3;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_27);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_47;
}
lean_ctor_set(x_52, 0, x_26);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_24);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_24, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_dec(x_24);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_20);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scc");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_DefView___hyg_963____closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_120; lean_object* x_121; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = lean_st_ref_get(x_8, x_9);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_138, 3);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_ctor_get_uint8(x_139, sizeof(void*)*1);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = 0;
x_120 = x_142;
x_121 = x_141;
goto block_136;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_137, 1);
lean_inc(x_143);
lean_dec(x_137);
x_144 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__2;
x_145 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_144, x_2, x_3, x_5, x_6, x_7, x_8, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_unbox(x_146);
lean_dec(x_146);
x_120 = x_148;
x_121 = x_147;
goto block_136;
}
block_119:
{
lean_object* x_11; lean_object* x_28; lean_object* x_29; lean_object* x_50; uint8_t x_51; 
x_28 = lean_array_get_size(x_1);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_dec_eq(x_28, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_lt(x_52, x_28);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_29 = x_54;
goto block_49;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_28, x_28);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_29 = x_56;
goto block_49;
}
else
{
size_t x_57; uint8_t x_58; 
x_57 = lean_usize_of_nat(x_28);
x_58 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(x_1, x_4, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_29 = x_59;
goto block_49;
}
else
{
lean_object* x_60; 
lean_dec(x_28);
x_60 = l_Lean_Elab_addAndCompileUnsafe(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
return x_60;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_60, 0);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_60);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = l_Lean_Elab_instInhabitedPreDefinition;
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_array_get(x_71, x_1, x_72);
lean_inc(x_73);
x_74 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_isNonRecursive(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_73);
x_75 = lean_nat_dec_lt(x_72, x_28);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_29 = x_76;
goto block_49;
}
else
{
uint8_t x_77; 
x_77 = lean_nat_dec_le(x_28, x_28);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
x_29 = x_78;
goto block_49;
}
else
{
size_t x_79; uint8_t x_80; 
x_79 = lean_usize_of_nat(x_28);
x_80 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(x_1, x_4, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_box(0);
x_29 = x_81;
goto block_49;
}
else
{
lean_object* x_82; 
lean_dec(x_28);
x_82 = l_Lean_Elab_addAndCompileUnsafe(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
x_85 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_82, 0, x_85);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_82);
if (x_89 == 0)
{
return x_82;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_82, 0);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_82);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
}
else
{
lean_object* x_93; uint8_t x_94; 
lean_dec(x_28);
lean_dec(x_1);
x_93 = lean_ctor_get(x_73, 1);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_93, sizeof(void*)*2 + 1);
lean_dec(x_93);
if (x_94 == 0)
{
uint8_t x_95; lean_object* x_96; 
x_95 = 1;
x_96 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_73, x_95, x_2, x_3, x_5, x_6, x_7, x_8, x_10);
lean_dec(x_3);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
x_99 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_96, 0, x_99);
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_96);
if (x_103 == 0)
{
return x_96;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_96, 0);
x_105 = lean_ctor_get(x_96, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_96);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; lean_object* x_108; 
x_107 = 0;
x_108 = l___private_Lean_Elab_PreDefinition_Basic_0__Lean_Elab_addNonRecAux(x_73, x_107, x_2, x_3, x_5, x_6, x_7, x_8, x_10);
lean_dec(x_3);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
lean_dec(x_110);
x_111 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_108, 0, x_111);
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_dec(x_108);
x_113 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_108);
if (x_115 == 0)
{
return x_108;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_108, 0);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_108);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
block_27:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__2), 8, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = l___private_Lean_Meta_WHNF_0__Lean_Meta_reduceRec___rarg___lambda__2___closed__1;
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_mapErrorImp___rarg(x_15, x_12, x_5, x_6, x_7, x_8, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
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
block_49:
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_lt(x_30, x_28);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_28);
x_32 = lean_box(0);
x_11 = x_32;
goto block_27;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_28, x_28);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_28);
x_34 = lean_box(0);
x_11 = x_34;
goto block_27;
}
else
{
size_t x_35; uint8_t x_36; 
x_35 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_36 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(x_1, x_4, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(0);
x_11 = x_37;
goto block_27;
}
else
{
lean_object* x_38; 
x_38 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_10);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
}
block_136:
{
if (x_120 == 0)
{
x_10 = x_121;
goto block_119;
}
else
{
lean_object* x_122; size_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_122 = lean_array_get_size(x_1);
x_123 = lean_usize_of_nat(x_122);
lean_dec(x_122);
lean_inc(x_1);
x_124 = x_1;
x_125 = l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__6(x_123, x_4, x_124);
x_126 = x_125;
x_127 = lean_array_to_list(lean_box(0), x_126);
x_128 = l_List_map___at_Lean_Elab_addPreDefinitions___spec__7(x_127);
x_129 = l_Lean_MessageData_ofList(x_128);
lean_dec(x_128);
x_130 = l_Lean_KernelException_toMessageData___closed__15;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__2;
x_134 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_133, x_132, x_2, x_3, x_5, x_6, x_7, x_8, x_121);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_10 = x_135;
goto block_119;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_7(x_16, lean_box(0), x_14, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8(x_1, x_3, x_4, x_5, x_20, x_18, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8(lean_object* x_1, size_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_5 < x_4;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_7(x_16, lean_box(0), x_6, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
x_18 = lean_array_uget(x_3, x_5);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_box_usize(x_2);
lean_inc(x_8);
lean_inc(x_7);
x_21 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___boxed), 9, 4);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_7);
lean_closure_set(x_21, 2, x_8);
lean_closure_set(x_21, 3, x_20);
x_22 = lean_box_usize(x_5);
x_23 = lean_box_usize(x_2);
x_24 = lean_box_usize(x_4);
x_25 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__4___boxed), 13, 7);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_3);
lean_closure_set(x_25, 4, x_24);
lean_closure_set(x_25, 5, x_7);
lean_closure_set(x_25, 6, x_8);
x_26 = lean_apply_9(x_19, lean_box(0), lean_box(0), x_21, x_25, x_9, x_10, x_11, x_12, x_13);
return x_26;
}
}
}
lean_object* l_Lean_Elab_addPreDefinitions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs(x_1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__3;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8(x_20, x_11, x_17, x_19, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
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
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
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
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__4(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_addPreDefinitions___spec__5(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_addPreDefinitions___spec__6(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__4(x_1, x_14, x_15, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8(x_1, x_14, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural(lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_PreDefinition_Main(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_addAndCompilePartial___spec__1___lambda__2___closed__2);
l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___boxed__const__1 = _init_l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___boxed__const__1();
lean_mark_persistent(l___private_Lean_Util_SCC_0__Lean_SCC_sccAux___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__9___boxed__const__1);
l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__1 = _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__1();
lean_mark_persistent(l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__1);
l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__2 = _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__2();
lean_mark_persistent(l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_0__Lean_Elab_partitionPreDefs___spec__5___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_addPreDefinitions___spec__8___lambda__3___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
