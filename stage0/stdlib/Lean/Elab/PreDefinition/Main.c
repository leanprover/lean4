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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__28(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__9(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__14(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafeRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_4__collectMVarsAtPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_PreDefinition_inhabited;
lean_object* l_List_map___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__1(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_6__ensureNoUnassignedMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__19(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_collectMVarsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Elab_PreDefinition_Structural_7__elimRecursion_x3f___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__29___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___rarg___lambda__1(lean_object*);
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__1;
extern lean_object* l_Lean_Meta_getMVarsImp___closed__1;
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompileUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__23(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_4__collectMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___boxed(lean_object*);
lean_object* l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__28___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__16(lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs(lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(lean_object*, size_t, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1;
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__13(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_2__push___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__11(lean_object*, lean_object*);
lean_object* l_Lean_Elab_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___boxed(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__13___boxed(lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__9___boxed(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__27___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__18(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_5__getMVarsAtPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Elab_addPreDefinitions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_DefView_1__regTraceClasses___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__25(lean_object*);
lean_object* l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21___boxed(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_6__ensureNoUnassignedMVarsAtPreDef___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__29(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FoldConstsImpl_initCache;
lean_object* l_Lean_Elab_WFRecursion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__2;
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__1(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__15(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addPreDefinitions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__3;
lean_object* l_Std_AssocList_replace___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__17(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__26(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_Main_5__getMVarsAtPreDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__26___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Elab_PreDefinition_Structural_7__elimRecursion_x3f___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_st_ref_get(x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_11, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_19, 2);
lean_dec(x_22);
x_23 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_19, 2, x_23);
x_24 = lean_st_ref_set(x_11, x_19, x_20);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_13);
x_26 = l_Lean_Elab_mkInhabitantFor(x_13, x_4, x_5, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_6);
x_29 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_13);
lean_ctor_set(x_34, 3, x_2);
lean_ctor_set(x_34, 4, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_33);
x_35 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_36 = l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(x_34, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Elab_addAndCompileUnsafeRec(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
lean_dec(x_9);
lean_dec(x_8);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_26, 1);
lean_inc(x_44);
lean_dec(x_26);
x_45 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = l_Lean_TraceState_Inhabited___closed__1;
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_st_ref_set(x_11, x_53, x_20);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_13);
x_56 = l_Lean_Elab_mkInhabitantFor(x_13, x_4, x_5, x_8, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_6);
x_59 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_dec(x_1);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_13);
lean_ctor_set(x_64, 3, x_2);
lean_ctor_set(x_64, 4, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*5, x_63);
x_65 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_66 = l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(x_64, x_65, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Elab_addAndCompileUnsafeRec(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_67);
lean_dec(x_9);
lean_dec(x_8);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_dec(x_56);
x_75 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__1___boxed), 12, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__1___rarg(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2(x_2, x_3, x_4, x_14, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_7(x_15, lean_box(0), x_16, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_4);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__2), 9, 4);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_5);
lean_closure_set(x_20, 3, x_6);
x_21 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__3___boxed), 12, 6);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_6);
x_22 = lean_apply_9(x_19, lean_box(0), lean_box(0), x_20, x_21, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2(x_1, x_9, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; size_t x_103; size_t x_104; lean_object* x_105; size_t x_106; uint8_t x_107; 
x_103 = lean_ptr_addr(x_3);
x_104 = x_2 == 0 ? 0 : x_103 % x_2;
x_105 = lean_array_uget(x_4, x_104);
x_106 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_107 = x_106 == x_103;
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
lean_inc(x_3);
x_108 = lean_array_uset(x_4, x_104, x_3);
x_109 = 0;
x_5 = x_109;
x_6 = x_108;
goto block_102;
}
else
{
uint8_t x_110; 
x_110 = 1;
x_5 = x_110;
x_6 = x_4;
goto block_102;
}
block_102:
{
lean_object* x_7; 
if (x_5 == 0)
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_3, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 2);
x_95 = lean_name_eq(x_94, x_93);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_box(0);
x_7 = x_96;
goto block_92;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_3);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_6);
return x_98;
}
}
else
{
lean_object* x_99; 
x_99 = lean_box(0);
x_7 = x_99;
goto block_92;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_6);
return x_101;
}
block_92:
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(x_1, x_2, x_8, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_3 = x_9;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_21 = x_11;
} else {
 lean_dec_ref(x_11);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(x_1, x_2, x_24, x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_3 = x_25;
x_4 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_25);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_37 = x_27;
} else {
 lean_dec_ref(x_27);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
case 7:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
lean_dec(x_3);
x_42 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(x_1, x_2, x_40, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_3 = x_41;
x_4 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_41);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
x_59 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(x_1, x_2, x_56, x_6);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(x_1, x_2, x_57, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_3 = x_58;
x_4 = x_64;
goto _start;
}
else
{
uint8_t x_66; 
lean_dec(x_58);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_62;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_62, 0, x_70);
return x_62;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_58);
lean_dec(x_57);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_59, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_59;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_60, 0);
lean_inc(x_79);
lean_dec(x_60);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_59, 0, x_80);
return x_59;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
lean_dec(x_59);
x_82 = lean_ctor_get(x_60, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_83 = x_60;
} else {
 lean_dec_ref(x_60);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
case 10:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
lean_dec(x_3);
x_3 = x_86;
x_4 = x_6;
goto _start;
}
case 11:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_3, 2);
lean_inc(x_88);
lean_dec(x_3);
x_3 = x_88;
x_4 = x_6;
goto _start;
}
default: 
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_6);
return x_91;
}
}
}
}
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
x_3 = 8192;
x_4 = l_Lean_Expr_FindImpl_initCache;
x_5 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(x_1, x_3, x_2, x_4);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__1(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; uint8_t x_72; 
x_66 = lean_ptr_addr(x_3);
x_67 = x_2 == 0 ? 0 : x_66 % x_2;
x_68 = lean_ctor_get(x_5, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_array_uget(x_68, x_67);
x_71 = lean_ptr_addr(x_70);
lean_dec(x_70);
x_72 = x_71 == x_66;
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_5, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_5, 0);
lean_dec(x_75);
lean_inc(x_3);
x_76 = lean_array_uset(x_68, x_67, x_3);
lean_ctor_set(x_5, 0, x_76);
x_77 = 0;
x_6 = x_77;
x_7 = x_5;
goto block_65;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_5);
lean_inc(x_3);
x_78 = lean_array_uset(x_68, x_67, x_3);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
x_80 = 0;
x_6 = x_80;
x_7 = x_79;
goto block_65;
}
}
else
{
uint8_t x_81; 
lean_dec(x_69);
lean_dec(x_68);
x_81 = 1;
x_6 = x_81;
x_7 = x_5;
goto block_65;
}
block_65:
{
if (x_6 == 0)
{
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_10, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
lean_inc(x_8);
x_15 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
lean_ctor_set(x_7, 1, x_15);
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3(x_1, x_8, x_1, x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
lean_inc(x_8);
x_22 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_get_size(x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3(x_1, x_8, x_1, x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
case 5:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_dec(x_3);
x_33 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(x_1, x_2, x_31, x_4, x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_3 = x_32;
x_4 = x_34;
x_5 = x_35;
goto _start;
}
case 6:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
lean_dec(x_3);
x_39 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(x_1, x_2, x_37, x_4, x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_3 = x_38;
x_4 = x_40;
x_5 = x_41;
goto _start;
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
lean_dec(x_3);
x_45 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(x_1, x_2, x_43, x_4, x_7);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_3 = x_44;
x_4 = x_46;
x_5 = x_47;
goto _start;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 3);
lean_inc(x_51);
lean_dec(x_3);
x_52 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(x_1, x_2, x_49, x_4, x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(x_1, x_2, x_50, x_53, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_3 = x_51;
x_4 = x_56;
x_5 = x_57;
goto _start;
}
case 10:
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
x_3 = x_59;
x_5 = x_7;
goto _start;
}
case 11:
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_3, 2);
lean_inc(x_61);
lean_dec(x_3);
x_3 = x_61;
x_5 = x_7;
goto _start;
}
default: 
{
lean_object* x_63; 
lean_dec(x_3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_7);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_7);
return x_64;
}
}
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; uint8_t x_72; 
x_66 = lean_ptr_addr(x_3);
x_67 = x_2 == 0 ? 0 : x_66 % x_2;
x_68 = lean_ctor_get(x_5, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
x_70 = lean_array_uget(x_68, x_67);
x_71 = lean_ptr_addr(x_70);
lean_dec(x_70);
x_72 = x_71 == x_66;
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_5, 1);
lean_dec(x_74);
x_75 = lean_ctor_get(x_5, 0);
lean_dec(x_75);
lean_inc(x_3);
x_76 = lean_array_uset(x_68, x_67, x_3);
lean_ctor_set(x_5, 0, x_76);
x_77 = 0;
x_6 = x_77;
x_7 = x_5;
goto block_65;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_5);
lean_inc(x_3);
x_78 = lean_array_uset(x_68, x_67, x_3);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
x_80 = 0;
x_6 = x_80;
x_7 = x_79;
goto block_65;
}
}
else
{
uint8_t x_81; 
lean_dec(x_69);
lean_dec(x_68);
x_81 = 1;
x_6 = x_81;
x_7 = x_5;
goto block_65;
}
block_65:
{
if (x_6 == 0)
{
switch (lean_obj_tag(x_3)) {
case 4:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = l_Std_HashSetImp_contains___at_Lean_NameHashSet_contains___spec__1(x_10, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_7, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
lean_inc(x_8);
x_15 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
lean_ctor_set(x_7, 1, x_15);
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3(x_1, x_8, x_1, x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
lean_inc(x_8);
x_22 = l_Std_HashSetImp_insert___at_Lean_NameHashSet_insert___spec__1(x_10, x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_get_size(x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3(x_1, x_8, x_1, x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
}
case 5:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_dec(x_3);
x_33 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(x_1, x_2, x_31, x_4, x_7);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_3 = x_32;
x_4 = x_34;
x_5 = x_35;
goto _start;
}
case 6:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
lean_dec(x_3);
x_39 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(x_1, x_2, x_37, x_4, x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_3 = x_38;
x_4 = x_40;
x_5 = x_41;
goto _start;
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 2);
lean_inc(x_44);
lean_dec(x_3);
x_45 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(x_1, x_2, x_43, x_4, x_7);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_3 = x_44;
x_4 = x_46;
x_5 = x_47;
goto _start;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 3);
lean_inc(x_51);
lean_dec(x_3);
x_52 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(x_1, x_2, x_49, x_4, x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(x_1, x_2, x_50, x_53, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_3 = x_51;
x_4 = x_56;
x_5 = x_57;
goto _start;
}
case 10:
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
lean_dec(x_3);
x_3 = x_59;
x_5 = x_7;
goto _start;
}
case 11:
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_3, 2);
lean_inc(x_61);
lean_dec(x_3);
x_3 = x_61;
x_5 = x_7;
goto _start;
}
default: 
{
lean_object* x_63; 
lean_dec(x_3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_7);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_3);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_7);
return x_64;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__9(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__9(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
x_4 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8(x_3, x_1);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Util_SCC_1__getDataOf___rarg___closed__1;
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
uint8_t l_Std_AssocList_contains___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__13(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__16(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__16(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__14(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__15(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_AssocList_replace___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__17(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_AssocList_replace___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__17(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Std_AssocList_contains___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__13(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__14(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__17(x_2, x_3, x_10);
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
x_26 = l_Std_AssocList_contains___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__13(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__14(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__17(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Util_SCC_2__push___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__11(lean_object* x_1, lean_object* x_2) {
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
x_13 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__12(x_6, x_1, x_12);
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
x_26 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__12(x_18, x_1, x_25);
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
lean_object* l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8(x_5, x_1);
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
x_11 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__12(x_5, x_1, x_10);
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
x_18 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8(x_16, x_1);
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
x_24 = l_Std_HashMapImp_insert___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__12(x_16, x_1, x_23);
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
lean_object* l___private_Lean_Util_SCC_5__updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_5__updateLowLinkOf___rarg___lambda__1), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__19(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_7, x_4);
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
x_13 = l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10(x_1, x_7, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_7, x_14);
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
x_19 = l___private_Lean_Util_SCC_5__updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__18(x_2, x_18, x_17);
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
x_26 = l___private_Lean_Util_SCC_5__updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__18(x_2, x_11, x_25);
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
lean_object* l___private_Lean_Util_SCC_4__resetOnStack___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__23(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Util_SCC_4__resetOnStack___rarg___closed__1;
x_4 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__19(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 3);
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_4, 3, x_8);
lean_ctor_set(x_4, 0, x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_4__resetOnStack___rarg___lambda__1), 1, 0);
lean_inc(x_19);
x_22 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__19(x_19, x_21, x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
lean_inc(x_19);
lean_ctor_set(x_2, 1, x_3);
x_26 = lean_name_eq(x_1, x_19);
lean_dec(x_19);
if (x_26 == 0)
{
lean_free_object(x_22);
{
lean_object* _tmp_1 = x_20;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_24;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 3);
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_24, 3, x_31);
lean_ctor_set(x_24, 0, x_20);
x_32 = lean_box(0);
lean_ctor_set(x_22, 0, x_32);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_24, 1);
x_34 = lean_ctor_get(x_24, 2);
x_35 = lean_ctor_get(x_24, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_box(0);
lean_ctor_set(x_22, 1, x_37);
lean_ctor_set(x_22, 0, x_38);
return x_22;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_dec(x_22);
lean_inc(x_19);
lean_ctor_set(x_2, 1, x_3);
x_40 = lean_name_eq(x_1, x_19);
lean_dec(x_19);
if (x_40 == 0)
{
{
lean_object* _tmp_1 = x_20;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_39;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_44);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 4, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_47, 3, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_2);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Util_SCC_4__resetOnStack___rarg___lambda__1), 1, 0);
lean_inc(x_50);
x_53 = l___private_Lean_Util_SCC_3__modifyDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__19(x_50, x_52, x_4);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
lean_inc(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_3);
x_57 = lean_name_eq(x_1, x_50);
lean_dec(x_50);
if (x_57 == 0)
{
lean_dec(x_55);
x_2 = x_51;
x_3 = x_56;
x_4 = x_54;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 3);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 4, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_box(0);
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
lean_object* l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l___private_Lean_Util_SCC_6__addSCCAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__22(x_1, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_7, x_4);
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
x_13 = l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10(x_1, x_7, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_7, x_14);
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
x_19 = l___private_Lean_Util_SCC_5__updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__18(x_2, x_18, x_17);
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
x_26 = l___private_Lean_Util_SCC_5__updateLowLinkOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__18(x_2, x_11, x_25);
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
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; 
lean_inc(x_2);
x_4 = l___private_Lean_Util_SCC_2__push___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__11(x_2, x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__2(x_2, x_1, x_6);
x_8 = lean_box(0);
x_9 = 8192;
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = l_Lean_Elab_PreDefinition_inhabited;
x_11 = l_Option_get_x21___rarg___closed__3;
x_12 = lean_panic_fn(x_10, x_11);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Expr_FoldConstsImpl_initCache;
x_15 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(x_1, x_9, x_13, x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
x_17 = l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__20(x_1, x_2, x_16, x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_2, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(x_2, x_23);
lean_dec(x_2);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_22);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_21);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_19, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_19, 0, x_34);
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_19, 1);
x_40 = lean_ctor_get(x_19, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_2);
x_44 = lean_box(0);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
else
{
lean_object* x_45; 
lean_free_object(x_19);
x_45 = l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(x_2, x_39);
lean_dec(x_2);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
lean_dec(x_21);
x_48 = lean_ctor_get(x_31, 0);
lean_inc(x_48);
lean_dec(x_31);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(x_2, x_46);
lean_dec(x_2);
return x_52;
}
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_7, 0);
lean_inc(x_53);
lean_dec(x_7);
x_54 = lean_ctor_get(x_53, 4);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Expr_FoldConstsImpl_initCache;
x_56 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(x_1, x_9, x_54, x_8, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_2);
x_58 = l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__24(x_1, x_2, x_57, x_5);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_2, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(x_2, x_64);
lean_dec(x_2);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_63);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_60, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_60, 0, x_68);
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_dec(x_60);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_61, 0);
lean_inc(x_72);
lean_dec(x_61);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
lean_dec(x_62);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_60, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_60, 0, x_75);
return x_60;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_dec(x_60);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_60);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_60, 1);
x_81 = lean_ctor_get(x_60, 0);
lean_dec(x_81);
x_82 = lean_ctor_get(x_62, 0);
lean_inc(x_82);
lean_dec(x_62);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_nat_dec_eq(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_2);
x_85 = lean_box(0);
lean_ctor_set(x_60, 0, x_85);
return x_60;
}
else
{
lean_object* x_86; 
lean_free_object(x_60);
x_86 = l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(x_2, x_80);
lean_dec(x_2);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_60, 1);
lean_inc(x_87);
lean_dec(x_60);
x_88 = lean_ctor_get(x_62, 0);
lean_inc(x_88);
lean_dec(x_62);
x_89 = lean_ctor_get(x_72, 0);
lean_inc(x_89);
lean_dec(x_72);
x_90 = lean_nat_dec_eq(x_88, x_89);
lean_dec(x_89);
lean_dec(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
else
{
lean_object* x_93; 
x_93 = l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(x_2, x_87);
lean_dec(x_2);
return x_93;
}
}
}
}
}
}
}
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__25(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_6, x_3);
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
x_12 = l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10(x_1, x_6, x_11);
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
lean_object* _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__2;
x_4 = l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__26(x_1, x_2, x_3);
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
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__27(x_10, x_1, x_8);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Elab_PreDefinition_inhabited;
x_15 = l_Option_get_x21___rarg___closed__3;
x_16 = lean_panic_fn(x_14, x_15);
x_17 = x_16;
x_18 = lean_array_fset(x_9, x_2, x_17);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = x_20;
x_22 = lean_array_fset(x_9, x_2, x_21);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_List_redLength___main___rarg(x_10);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
x_13 = l_List_toArrayAux___main___rarg(x_10, x_12);
x_14 = x_13;
x_15 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__28(x_1, x_8, x_14);
x_16 = x_15;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = x_16;
x_20 = lean_array_fset(x_9, x_2, x_19);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_20;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_Array_toList___rarg(x_1);
x_3 = l_List_map___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__1(x_2);
x_4 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6(x_1, x_3);
x_5 = l_List_redLength___main___rarg(x_4);
x_6 = lean_mk_empty_array_with_capacity(x_5);
lean_dec(x_5);
x_7 = l_List_toArrayAux___main___rarg(x_4, x_6);
x_8 = x_7;
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__29(x_1, x_9, x_8);
x_11 = x_10;
return x_11;
}
}
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__4(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Lean_Expr_FoldConstsImpl_fold___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__5(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__9(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_SCC_1__getDataOf___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__13(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__20(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Util_SCC_6__addSCCAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Util_SCC_6__addSCCAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__22(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_SCC_7__addSCC___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__21(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__24(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Util_SCC_8__sccAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__10(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__26(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__27(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__28(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__29(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_4__collectMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = l_Lean_Meta_collectMVarsAux___main(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_collectMVarsAux___main(x_11, x_2, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_4__collectMVarsAtPreDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PreDefinition_Main_4__collectMVarsAtPreDef(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_5__getMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = l_Lean_Meta_getMVarsImp___closed__1;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Elab_PreDefinition_Main_4__collectMVarsAtPreDef(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
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
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_5__getMVarsAtPreDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Main_5__getMVarsAtPreDef(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_6__ensureNoUnassignedMVarsAtPreDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_7, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
x_18 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_14, 2, x_18);
x_19 = lean_st_ref_set(x_7, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l___private_Lean_Elab_PreDefinition_Main_5__getMVarsAtPreDef(x_1, x_4, x_5, x_6, x_7, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Elab_Term_logUnassignedUsingErrorContext(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = l_Lean_TraceState_Inhabited___closed__1;
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_st_ref_set(x_7, x_40, x_15);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l___private_Lean_Elab_PreDefinition_Main_5__getMVarsAtPreDef(x_1, x_4, x_5, x_6, x_7, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_2);
x_46 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Term_logUnassignedUsingErrorContext(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_Elab_throwAbort___at_Lean_Elab_Term_ensureNoUnassignedMVars___spec__2___rarg(x_55);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Main_6__ensureNoUnassignedMVarsAtPreDef___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_Main_6__ensureNoUnassignedMVarsAtPreDef(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("body");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_DefView_1__regTraceClasses___closed__2;
x_2 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_array_fget(x_1, x_2);
x_15 = lean_ctor_get(x_7, 0);
x_16 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__2;
x_17 = l_Lean_checkTraceOption(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_14, 2);
lean_inc(x_21);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_ctor_get(x_14, 3);
lean_inc(x_25);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__3;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofList___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_ctor_get(x_14, 4);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_16, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_2, x_37);
lean_dec(x_2);
x_2 = x_38;
x_9 = x_36;
goto _start;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
lean_inc(x_3);
x_15 = l___private_Lean_Elab_PreDefinition_Main_6__ensureNoUnassignedMVarsAtPreDef(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_2);
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
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_lt(x_2, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_array_fget(x_1, x_2);
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__3(x_24, x_24, x_25, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__4(x_24, x_24, x_25, x_28);
lean_dec(x_25);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Elab_structuralRecursion(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_3);
x_35 = l_Lean_Elab_WFRecursion___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_34);
x_10 = x_35;
goto block_19;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_31, 0, x_38);
x_10 = x_31;
goto block_19;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_10 = x_41;
goto block_19;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
x_10 = x_31;
goto block_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_10 = x_45;
goto block_19;
}
}
}
else
{
lean_object* x_46; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_10 = x_46;
goto block_19;
}
}
else
{
lean_object* x_47; 
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_47 = l_Lean_Elab_addAndCompileUnsafe(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_24);
x_10 = x_47;
goto block_19;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = l_Lean_Elab_PreDefinition_inhabited;
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get(x_48, x_24, x_49);
lean_inc(x_50);
x_51 = l___private_Lean_Elab_PreDefinition_Main_2__isNonRecursive(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_50);
x_52 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__5(x_24, x_24, x_25, x_49);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__6(x_24, x_24, x_25, x_49);
lean_dec(x_25);
if (x_53 == 0)
{
lean_object* x_54; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_54 = l_Lean_Elab_structuralRecursion(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_inc(x_3);
x_58 = l_Lean_Elab_WFRecursion___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_57);
x_10 = x_58;
goto block_19;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_54, 0, x_61);
x_10 = x_54;
goto block_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_10 = x_64;
goto block_19;
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_54);
if (x_65 == 0)
{
x_10 = x_54;
goto block_19;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_54, 0);
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_54);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_10 = x_68;
goto block_19;
}
}
}
else
{
lean_object* x_69; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = l___private_Lean_Elab_PreDefinition_Main_1__addAndCompilePartial(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_10 = x_69;
goto block_19;
}
}
else
{
lean_object* x_70; 
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_70 = l_Lean_Elab_addAndCompileUnsafe(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_24);
x_10 = x_70;
goto block_19;
}
}
else
{
uint8_t x_71; lean_object* x_72; 
lean_dec(x_25);
lean_dec(x_24);
x_71 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_72 = l___private_Lean_Elab_PreDefinition_Basic_6__addNonRecAux(x_50, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_10 = x_72;
goto block_19;
}
}
}
block_19:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_9 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* l_Lean_Elab_addPreDefinitions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_2);
x_12 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__2(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs(x_1);
x_15 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__7(x_14, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_addPreDefinitions___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_addPreDefinitions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_addPreDefinitions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
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
l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__1 = _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__1();
lean_mark_persistent(l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__1);
l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__2 = _init_l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__2();
lean_mark_persistent(l_Lean_SCC_scc___at___private_Lean_Elab_PreDefinition_Main_3__partitionPreDefs___spec__6___closed__2);
l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__1 = _init_l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__1);
l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__2 = _init_l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__2);
l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__3 = _init_l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at_Lean_Elab_addPreDefinitions___spec__1___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
