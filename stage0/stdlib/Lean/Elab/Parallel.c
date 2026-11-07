// Lean compiler output
// Module: Lean.Elab.Parallel
// Imports: public import Lean.Elab.Task
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
lean_object* l_IO_waitAny_x27___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_asTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_unzipTR___redArg(lean_object*);
lean_object* l_Lean_Core_CoreM_asTask___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_saveState___redArg(lean_object*);
lean_object* l_Lean_Meta_MetaM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_TacticM_asTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MetaM_asTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_CoreM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Core_CoreM_parFirst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "All parallel tasks failed"};
static const lean_object* l_Lean_Core_CoreM_parFirst___redArg___closed__0 = (const lean_object*)&l_Lean_Core_CoreM_parFirst___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Core_CoreM_parFirst___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Core_CoreM_parFirst___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0(lean_object* v_it_1_){
_start:
{
if (lean_obj_tag(v_it_1_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(2);
return v___x_3_;
}
else
{
lean_object* v___x_4_; lean_object* v_fst_5_; lean_object* v_snd_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_13_; 
v___x_4_ = l_IO_waitAny_x27___redArg(v_it_1_);
v_fst_5_ = lean_ctor_get(v___x_4_, 0);
v_snd_6_ = lean_ctor_get(v___x_4_, 1);
v_isSharedCheck_13_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_13_ == 0)
{
v___x_8_ = v___x_4_;
v_isShared_9_ = v_isSharedCheck_13_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_snd_6_);
lean_inc(v_fst_5_);
lean_dec(v___x_4_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_13_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_11_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_fst_5_);
lean_ctor_set(v___x_8_, 0, v_snd_6_);
v___x_11_ = v___x_8_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_snd_6_);
lean_ctor_set(v_reuseFailAlloc_12_, 1, v_fst_5_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0___boxed(lean_object* v_it_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0(v_it_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg(){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = ((lean_object*)(l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___closed__0));
return v___f_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___boxed(lean_object* v___dummy_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg();
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO(lean_object* v_00_u03b1_22_){
_start:
{
lean_object* v___f_23_; 
v___f_23_ = ((lean_object*)(l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___closed__0));
return v___f_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(lean_object* v_tasks_24_){
_start:
{
lean_inc(v_tasks_24_);
return v_tasks_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg___boxed(lean_object* v_tasks_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(v_tasks_25_);
lean_dec(v_tasks_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks(lean_object* v_00_u03b1_27_, lean_object* v_tasks_28_){
_start:
{
lean_inc(v_tasks_28_);
return v_tasks_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___boxed(lean_object* v_00_u03b1_29_, lean_object* v_tasks_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks(v_00_u03b1_29_, v_tasks_30_);
lean_dec(v_tasks_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = l_List_reverse___redArg(v_x_33_);
v___x_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
return v___x_38_;
}
else
{
lean_object* v_head_39_; lean_object* v_tail_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_58_; 
v_head_39_ = lean_ctor_get(v_x_32_, 0);
v_tail_40_ = lean_ctor_get(v_x_32_, 1);
v_isSharedCheck_58_ = !lean_is_exclusive(v_x_32_);
if (v_isSharedCheck_58_ == 0)
{
v___x_42_ = v_x_32_;
v_isShared_43_ = v_isSharedCheck_58_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_tail_40_);
lean_inc(v_head_39_);
lean_dec(v_x_32_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_58_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Core_CoreM_asTask___redArg(v_head_39_, v___y_34_, v___y_35_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v___x_47_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_44_, 1);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v_x_33_);
lean_ctor_set(v___x_42_, 0, v_a_45_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_x_33_);
v___x_47_ = v_reuseFailAlloc_49_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
v_x_32_ = v_tail_40_;
v_x_33_ = v___x_47_;
goto _start;
}
}
else
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
lean_del_object(v___x_42_);
lean_dec(v_tail_40_);
lean_dec(v_x_33_);
v_a_50_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_44_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_44_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_x_59_, v_x_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(lean_object* v_as_65_){
_start:
{
if (lean_obj_tag(v_as_65_) == 0)
{
lean_object* v___x_67_; 
v___x_67_ = lean_box(0);
return v___x_67_;
}
else
{
lean_object* v_head_68_; lean_object* v_tail_69_; lean_object* v___x_70_; 
v_head_68_ = lean_ctor_get(v_as_65_, 0);
lean_inc(v_head_68_);
v_tail_69_ = lean_ctor_get(v_as_65_, 1);
lean_inc(v_tail_69_);
lean_dec_ref_known(v_as_65_, 2);
v___x_70_ = lean_apply_1(v_head_68_, lean_box(0));
v_as_65_ = v_tail_69_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed(lean_object* v_as_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(v_as_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg(lean_object* v_jobs_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_box(0);
v___x_80_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_jobs_75_, v___x_79_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_99_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_99_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v_fst_86_; lean_object* v_snd_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_98_; 
v___x_85_ = l_List_unzipTR___redArg(v_a_81_);
v_fst_86_ = lean_ctor_get(v___x_85_, 0);
v_snd_87_ = lean_ctor_get(v___x_85_, 1);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_98_ == 0)
{
v___x_89_ = v___x_85_;
v_isShared_90_ = v_isSharedCheck_98_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_snd_87_);
lean_inc(v_fst_86_);
lean_dec(v___x_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_98_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_91_, 0, v_fst_86_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_snd_87_);
v___x_93_ = v_reuseFailAlloc_97_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___x_93_);
v___x_95_ = v___x_83_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_a_100_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_80_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_80_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_108_, v_a_109_, v_a_110_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel(lean_object* v_00_u03b1_113_, lean_object* v_jobs_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_114_, v_a_115_, v_a_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___boxed(lean_object* v_00_u03b1_119_, lean_object* v_jobs_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Core_CoreM_parIterWithCancel(v_00_u03b1_119_, v_jobs_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_125_, lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_x_126_, v_x_127_, v___y_128_, v___y_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_132_, lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(v_00_u03b1_132_, v_x_133_, v_x_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___redArg(lean_object* v_jobs_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_139_, v_a_140_, v_a_141_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_152_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_152_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_152_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_snd_148_; lean_object* v___x_150_; 
v_snd_148_ = lean_ctor_get(v_a_144_, 1);
lean_inc(v_snd_148_);
lean_dec(v_a_144_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v_snd_148_);
v___x_150_ = v___x_146_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_snd_148_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v_a_153_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_143_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_143_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___redArg___boxed(lean_object* v_jobs_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter(lean_object* v_00_u03b1_166_, lean_object* v_jobs_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_167_, v_a_168_, v_a_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___boxed(lean_object* v_00_u03b1_172_, lean_object* v_jobs_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Core_CoreM_parIter(v_00_u03b1_172_, v_jobs_173_, v_a_174_, v_a_175_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(0);
v___x_183_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_jobs_178_, v___x_182_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_202_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_202_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_202_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_202_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v_fst_189_; lean_object* v_snd_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_201_; 
v___x_188_ = l_List_unzipTR___redArg(v_a_184_);
v_fst_189_ = lean_ctor_get(v___x_188_, 0);
v_snd_190_ = lean_ctor_get(v___x_188_, 1);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_201_ == 0)
{
v___x_192_ = v___x_188_;
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_snd_190_);
lean_inc(v_fst_189_);
lean_dec(v___x_188_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_201_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_194_, 0, v_fst_189_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_snd_190_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_196_);
v___x_198_ = v___x_186_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_183_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_183_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel(lean_object* v_00_u03b1_216_, lean_object* v_jobs_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_217_, v_a_218_, v_a_219_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_222_, lean_object* v_jobs_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Core_CoreM_parIterGreedyWithCancel(v_00_u03b1_222_, v_jobs_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg(lean_object* v_jobs_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_snd_237_; lean_object* v___x_239_; 
v_snd_237_ = lean_ctor_get(v_a_233_, 1);
lean_inc(v_snd_237_);
lean_dec(v_a_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v_snd_237_);
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_snd_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_232_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_232_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg___boxed(lean_object* v_jobs_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_250_, v_a_251_, v_a_252_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy(lean_object* v_00_u03b1_255_, lean_object* v_jobs_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_256_, v_a_257_, v_a_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___boxed(lean_object* v_00_u03b1_261_, lean_object* v_jobs_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Core_CoreM_parIterGreedy(v_00_u03b1_261_, v_jobs_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(lean_object* v_as_x27_267_, lean_object* v_b_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
if (lean_obj_tag(v_as_x27_267_) == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v_b_268_);
return v___x_272_;
}
else
{
lean_object* v_head_273_; lean_object* v_tail_274_; lean_object* v_a_276_; lean_object* v_a_280_; lean_object* v___x_1791__overap_286_; lean_object* v___x_287_; 
v_head_273_ = lean_ctor_get(v_as_x27_267_, 0);
v_tail_274_ = lean_ctor_get(v_as_x27_267_, 1);
lean_inc(v_head_273_);
v___x_1791__overap_286_ = lean_task_get_own(v_head_273_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
v___x_287_ = lean_apply_3(v___x_1791__overap_286_, v___y_269_, v___y_270_, lean_box(0));
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_289_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_287_, 1);
v___x_289_ = l_Lean_Core_saveState___redArg(v___y_270_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_298_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_a_288_);
lean_ctor_set(v___x_294_, 1, v_a_290_);
if (v_isShared_293_ == 0)
{
lean_ctor_set_tag(v___x_292_, 1);
lean_ctor_set(v___x_292_, 0, v___x_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
v_a_276_ = v___x_296_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v_a_299_; 
lean_dec(v_a_288_);
v_a_299_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_289_, 1);
v_a_280_ = v_a_299_;
goto v___jp_279_;
}
}
else
{
lean_object* v_a_300_; 
v_a_300_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_287_, 1);
v_a_280_ = v_a_300_;
goto v___jp_279_;
}
v___jp_275_:
{
lean_object* v___x_277_; 
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v_a_276_);
lean_ctor_set(v___x_277_, 1, v_b_268_);
v_as_x27_267_ = v_tail_274_;
v_b_268_ = v___x_277_;
goto _start;
}
v___jp_279_:
{
uint8_t v___x_281_; 
v___x_281_ = l_Lean_Exception_isInterrupt(v_a_280_);
if (v___x_281_ == 0)
{
uint8_t v___x_282_; 
lean_inc_ref(v_a_280_);
v___x_282_ = l_Lean_Exception_isRuntime(v_a_280_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v_a_280_);
v_a_276_ = v___x_283_;
goto v___jp_275_;
}
else
{
lean_object* v___x_284_; 
lean_dec(v_b_268_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v_a_280_);
return v___x_284_;
}
}
else
{
lean_object* v___x_285_; 
lean_dec(v_b_268_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_a_280_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg___boxed(lean_object* v_as_x27_301_, lean_object* v_b_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_301_, v_b_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v_as_x27_301_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
if (lean_obj_tag(v_x_307_) == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = l_List_reverse___redArg(v_x_308_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v_head_314_; lean_object* v_tail_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_333_; 
v_head_314_ = lean_ctor_get(v_x_307_, 0);
v_tail_315_ = lean_ctor_get(v_x_307_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_307_);
if (v_isSharedCheck_333_ == 0)
{
v___x_317_ = v_x_307_;
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_tail_315_);
lean_inc(v_head_314_);
lean_dec(v_x_307_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_head_314_, v___y_309_, v___y_310_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; lean_object* v___x_322_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v_x_308_);
lean_ctor_set(v___x_317_, 0, v_a_320_);
v___x_322_ = v___x_317_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_320_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_x_308_);
v___x_322_ = v_reuseFailAlloc_324_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
v_x_307_ = v_tail_315_;
v_x_308_ = v___x_322_;
goto _start;
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_del_object(v___x_317_);
lean_dec(v_tail_315_);
lean_dec(v_x_308_);
v_a_325_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_319_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_319_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg___boxed(lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_334_, v_x_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg(lean_object* v_jobs_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_st_ref_get(v_a_342_);
v___x_345_ = lean_box(0);
v___x_346_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_340_, v___x_345_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_a_347_, v___x_345_, v_a_341_, v_a_342_);
lean_dec(v_a_347_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_358_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_358_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_358_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_353_ = lean_st_ref_swap(v_a_342_, v___x_344_);
lean_dec(v___x_353_);
v___x_354_ = l_List_reverse___redArg(v_a_349_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_354_);
v___x_356_ = v___x_351_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
else
{
lean_dec(v___x_344_);
return v___x_348_;
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v___x_344_);
v_a_359_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_346_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_346_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg___boxed(lean_object* v_jobs_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Core_CoreM_par___redArg(v_jobs_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par(lean_object* v_00_u03b1_372_, lean_object* v_jobs_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Core_CoreM_par___redArg(v_jobs_373_, v_a_374_, v_a_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___boxed(lean_object* v_00_u03b1_378_, lean_object* v_jobs_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Core_CoreM_par(v_00_u03b1_378_, v_jobs_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(lean_object* v_00_u03b1_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_385_, v_x_386_, v___y_387_, v___y_388_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___boxed(lean_object* v_00_u03b1_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(v_00_u03b1_391_, v_x_392_, v_x_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(lean_object* v_00_u03b1_398_, lean_object* v_as_399_, lean_object* v_as_x27_400_, lean_object* v_b_401_, lean_object* v_a_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_400_, v_b_401_, v___y_403_, v___y_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___boxed(lean_object* v_00_u03b1_407_, lean_object* v_as_408_, lean_object* v_as_x27_409_, lean_object* v_b_410_, lean_object* v_a_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(v_00_u03b1_407_, v_as_408_, v_as_x27_409_, v_b_410_, v_a_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v_as_x27_409_);
lean_dec(v_as_408_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(lean_object* v_as_x27_416_, lean_object* v_b_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
if (lean_obj_tag(v_as_x27_416_) == 0)
{
lean_object* v___x_421_; 
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v_b_417_);
return v___x_421_;
}
else
{
lean_object* v_head_422_; lean_object* v_tail_423_; lean_object* v___x_1601__overap_424_; lean_object* v___x_425_; 
v_head_422_ = lean_ctor_get(v_as_x27_416_, 0);
v_tail_423_ = lean_ctor_get(v_as_x27_416_, 1);
lean_inc(v_head_422_);
v___x_1601__overap_424_ = lean_task_get_own(v_head_422_);
lean_inc(v___y_419_);
lean_inc_ref(v___y_418_);
v___x_425_ = lean_apply_3(v___x_1601__overap_424_, v___y_418_, v___y_419_, lean_box(0));
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v___x_425_, 1);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_a_426_);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v_b_417_);
v_as_x27_416_ = v_tail_423_;
v_b_417_ = v___x_428_;
goto _start;
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_445_; 
v_a_430_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_445_ == 0)
{
v___x_432_ = v___x_425_;
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_425_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
uint8_t v___x_434_; 
v___x_434_ = l_Lean_Exception_isInterrupt(v_a_430_);
if (v___x_434_ == 0)
{
uint8_t v___x_435_; 
lean_inc(v_a_430_);
v___x_435_ = l_Lean_Exception_isRuntime(v_a_430_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_del_object(v___x_432_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v_a_430_);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v_b_417_);
v_as_x27_416_ = v_tail_423_;
v_b_417_ = v___x_437_;
goto _start;
}
else
{
lean_object* v___x_440_; 
lean_dec(v_b_417_);
if (v_isShared_433_ == 0)
{
v___x_440_ = v___x_432_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_430_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v_b_417_);
if (v_isShared_433_ == 0)
{
v___x_443_ = v___x_432_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_430_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_446_, v_b_447_, v___y_448_, v___y_449_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v_as_x27_446_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg(lean_object* v_jobs_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_st_ref_get(v_a_454_);
v___x_457_ = lean_box(0);
v___x_458_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_452_, v___x_457_, v_a_453_, v_a_454_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v___x_460_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_a_459_, v___x_457_, v_a_453_, v_a_454_);
lean_dec(v_a_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_470_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_470_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_470_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_465_ = lean_st_ref_swap(v_a_454_, v___x_456_);
lean_dec(v___x_465_);
v___x_466_ = l_List_reverse___redArg(v_a_461_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
else
{
lean_dec(v___x_456_);
return v___x_460_;
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v___x_456_);
v_a_471_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_458_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_458_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg___boxed(lean_object* v_jobs_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27(lean_object* v_00_u03b1_484_, lean_object* v_jobs_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_485_, v_a_486_, v_a_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___boxed(lean_object* v_00_u03b1_490_, lean_object* v_jobs_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Core_CoreM_par_x27(v_00_u03b1_490_, v_jobs_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(lean_object* v_00_u03b1_496_, lean_object* v_as_497_, lean_object* v_as_x27_498_, lean_object* v_b_499_, lean_object* v_a_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_498_, v_b_499_, v___y_501_, v___y_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_505_, lean_object* v_as_506_, lean_object* v_as_x27_507_, lean_object* v_b_508_, lean_object* v_a_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(v_00_u03b1_505_, v_as_506_, v_as_x27_507_, v_b_508_, v_a_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v_as_x27_507_);
lean_dec(v_as_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_514_, lean_object* v___x_515_, lean_object* v_____r_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v_a_514_);
v___x_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_515_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_524_, lean_object* v___x_525_, lean_object* v_____r_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_524_, v___x_525_, v_____r_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(uint8_t v_cancel_534_, lean_object* v_fst_535_, lean_object* v_a_536_, lean_object* v_b_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
if (lean_obj_tag(v_a_536_) == 0)
{
lean_object* v___x_541_; 
lean_dec_ref(v_fst_535_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_b_537_);
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_fst_545_; lean_object* v_snd_546_; lean_object* v___y_548_; lean_object* v___x_568_; 
lean_dec_ref(v_b_537_);
v___x_542_ = lean_box(0);
v___x_543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_544_ = l_IO_waitAny_x27___redArg(v_a_536_);
v_fst_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_fst_545_);
v_snd_546_ = lean_ctor_get(v___x_544_, 1);
lean_inc(v_snd_546_);
lean_dec_ref(v___x_544_);
lean_inc(v___y_539_);
lean_inc_ref(v___y_538_);
v___x_568_ = lean_apply_3(v_fst_545_, v___y_538_, v___y_539_, lean_box(0));
if (lean_obj_tag(v___x_568_) == 0)
{
if (v_cancel_534_ == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
lean_dec_ref_known(v___x_568_, 1);
v___x_570_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_569_, v___x_542_, v___x_542_, v___y_538_, v___y_539_);
v___y_548_ = v___x_570_;
goto v___jp_547_;
}
else
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_a_571_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_568_, 1);
lean_inc_ref(v_fst_535_);
v___x_572_ = lean_apply_1(v_fst_535_, lean_box(0));
v___x_573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_571_, v___x_542_, v___x_572_, v___y_538_, v___y_539_);
v___y_548_ = v___x_573_;
goto v___jp_547_;
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_587_; 
v_a_574_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_587_ == 0)
{
v___x_576_ = v___x_568_;
v_isShared_577_ = v_isSharedCheck_587_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_568_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_587_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
uint8_t v___x_578_; 
v___x_578_ = l_Lean_Exception_isInterrupt(v_a_574_);
if (v___x_578_ == 0)
{
uint8_t v___x_579_; 
lean_inc(v_a_574_);
v___x_579_ = l_Lean_Exception_isRuntime(v_a_574_);
if (v___x_579_ == 0)
{
lean_del_object(v___x_576_);
lean_dec(v_a_574_);
v_a_536_ = v_snd_546_;
v_b_537_ = v___x_543_;
goto _start;
}
else
{
lean_object* v___x_582_; 
lean_dec(v_snd_546_);
lean_dec_ref(v_fst_535_);
if (v_isShared_577_ == 0)
{
v___x_582_ = v___x_576_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_574_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_object* v___x_585_; 
lean_dec(v_snd_546_);
lean_dec_ref(v_fst_535_);
if (v_isShared_577_ == 0)
{
v___x_585_ = v___x_576_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_574_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
v___jp_547_:
{
if (lean_obj_tag(v___y_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
v_a_549_ = lean_ctor_get(v___y_548_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___y_548_);
if (v_isSharedCheck_559_ == 0)
{
v___x_551_ = v___y_548_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___y_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
if (lean_obj_tag(v_a_549_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; 
lean_dec(v_snd_546_);
lean_dec_ref(v_fst_535_);
v_a_553_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v_a_549_, 1);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v_a_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
else
{
lean_object* v_a_557_; 
lean_del_object(v___x_551_);
v_a_557_ = lean_ctor_get(v_a_549_, 0);
lean_inc(v_a_557_);
lean_dec_ref_known(v_a_549_, 1);
v_a_536_ = v_snd_546_;
v_b_537_ = v_a_557_;
goto _start;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_snd_546_);
lean_dec_ref(v_fst_535_);
v_a_560_ = lean_ctor_get(v___y_548_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___y_548_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___y_548_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___y_548_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_588_, lean_object* v_fst_589_, lean_object* v_a_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v_cancel_boxed_595_; lean_object* v_res_596_; 
v_cancel_boxed_595_ = lean_unbox(v_cancel_588_);
v_res_596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_boxed_595_, v_fst_589_, v_a_590_, v_b_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_596_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_597_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
lean_ctor_set(v___x_602_, 2, v___x_601_);
lean_ctor_set(v___x_602_, 3, v___x_601_);
lean_ctor_set(v___x_602_, 4, v___x_600_);
lean_ctor_set(v___x_602_, 5, v___x_600_);
lean_ctor_set(v___x_602_, 6, v___x_600_);
lean_ctor_set(v___x_602_, 7, v___x_600_);
lean_ctor_set(v___x_602_, 8, v___x_600_);
lean_ctor_set(v___x_602_, 9, v___x_600_);
lean_ctor_set(v___x_602_, 10, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(32u);
v___x_604_ = lean_mk_empty_array_with_capacity(v___x_603_);
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_606_ = ((size_t)5ULL);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_unsigned_to_nat(32u);
v___x_609_ = lean_mk_empty_array_with_capacity(v___x_608_);
v___x_610_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3);
v___x_611_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_607_);
lean_ctor_set(v___x_611_, 3, v___x_607_);
lean_ctor_set_usize(v___x_611_, 4, v___x_606_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = lean_box(1);
v___x_613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4);
v___x_614_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
lean_ctor_set(v___x_615_, 2, v___x_612_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(lean_object* v_msgData_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v_toCold_621_; lean_object* v_env_622_; lean_object* v_options_623_; uint8_t v___x_624_; lean_object* v_env_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_620_ = lean_st_ref_get(v___y_618_);
v_toCold_621_ = lean_ctor_get(v___y_617_, 0);
v_env_622_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref(v_env_622_);
lean_dec(v___x_620_);
v_options_623_ = lean_ctor_get(v_toCold_621_, 2);
v___x_624_ = 0;
v_env_625_ = l_Lean_Environment_setRecordingDeps(v_env_622_, v___x_624_);
v___x_626_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2);
v___x_627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_623_);
v___x_628_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_628_, 0, v_env_625_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set(v___x_628_, 3, v_options_623_);
v___x_629_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_msgData_616_);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msgData_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_ref_640_; lean_object* v___x_641_; lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_650_; 
v_ref_640_ = lean_ctor_get(v___y_637_, 2);
v___x_641_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msg_636_, v___y_637_, v___y_638_);
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_650_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_650_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
lean_inc(v_ref_640_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_ref_640_);
lean_ctor_set(v___x_646_, 1, v_a_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 1);
lean_ctor_set(v___x_644_, 0, v___x_646_);
v___x_648_ = v___x_644_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_655_;
}
}
static lean_object* _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Core_CoreM_parFirst___redArg___closed__0));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg(lean_object* v_jobs_659_, uint8_t v_cancel_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_659_, v_a_661_, v_a_662_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; lean_object* v_fst_666_; lean_object* v_snd_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v_fst_666_ = lean_ctor_get(v_a_665_, 0);
lean_inc(v_fst_666_);
v_snd_667_ = lean_ctor_get(v_a_665_, 1);
lean_inc(v_snd_667_);
lean_dec(v_a_665_);
v___x_668_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_660_, v_fst_666_, v_snd_667_, v___x_668_, v_a_661_, v_a_662_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_681_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_681_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_681_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_681_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_fst_674_; 
v_fst_674_ = lean_ctor_get(v_a_670_, 0);
lean_inc(v_fst_674_);
lean_dec(v_a_670_);
if (lean_obj_tag(v_fst_674_) == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; 
lean_del_object(v___x_672_);
v___x_675_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_676_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v___x_675_, v_a_661_, v_a_662_);
return v___x_676_;
}
else
{
lean_object* v_val_677_; lean_object* v___x_679_; 
v_val_677_ = lean_ctor_get(v_fst_674_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_fst_674_, 1);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_val_677_);
v___x_679_ = v___x_672_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_val_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_a_682_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_669_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_669_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
v_a_690_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_664_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_664_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg___boxed(lean_object* v_jobs_698_, lean_object* v_cancel_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
uint8_t v_cancel_boxed_703_; lean_object* v_res_704_; 
v_cancel_boxed_703_ = lean_unbox(v_cancel_699_);
v_res_704_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_698_, v_cancel_boxed_703_, v_a_700_, v_a_701_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst(lean_object* v_00_u03b1_705_, lean_object* v_jobs_706_, uint8_t v_cancel_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_706_, v_cancel_707_, v_a_708_, v_a_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___boxed(lean_object* v_00_u03b1_712_, lean_object* v_jobs_713_, lean_object* v_cancel_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
uint8_t v_cancel_boxed_718_; lean_object* v_res_719_; 
v_cancel_boxed_718_ = lean_unbox(v_cancel_714_);
v_res_719_ = l_Lean_Core_CoreM_parFirst(v_00_u03b1_712_, v_jobs_713_, v_cancel_boxed_718_, v_a_715_, v_a_716_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(lean_object* v_00_u03b1_720_, uint8_t v_cancel_721_, lean_object* v_fst_722_, lean_object* v_inst_723_, lean_object* v_R_724_, lean_object* v_a_725_, lean_object* v_b_726_, lean_object* v_c_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_721_, v_fst_722_, v_a_725_, v_b_726_, v___y_728_, v___y_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_732_, lean_object* v_cancel_733_, lean_object* v_fst_734_, lean_object* v_inst_735_, lean_object* v_R_736_, lean_object* v_a_737_, lean_object* v_b_738_, lean_object* v_c_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
uint8_t v_cancel_boxed_743_; lean_object* v_res_744_; 
v_cancel_boxed_743_ = lean_unbox(v_cancel_733_);
v_res_744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(v_00_u03b1_732_, v_cancel_boxed_743_, v_fst_734_, v_inst_735_, v_R_736_, v_a_737_, v_b_738_, v_c_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(lean_object* v_00_u03b1_745_, lean_object* v_msg_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_746_, v___y_747_, v___y_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_751_, lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(v_00_u03b1_751_, v_msg_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
if (lean_obj_tag(v_x_757_) == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = l_List_reverse___redArg(v_x_758_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
else
{
lean_object* v_head_766_; lean_object* v_tail_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_785_; 
v_head_766_ = lean_ctor_get(v_x_757_, 0);
v_tail_767_ = lean_ctor_get(v_x_757_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_x_757_);
if (v_isSharedCheck_785_ == 0)
{
v___x_769_ = v_x_757_;
v_isShared_770_ = v_isSharedCheck_785_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_tail_767_);
lean_inc(v_head_766_);
lean_dec(v_x_757_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_785_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_head_766_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_x_758_);
lean_ctor_set(v___x_769_, 0, v_a_772_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_772_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_x_758_);
v___x_774_ = v_reuseFailAlloc_776_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
v_x_757_ = v_tail_767_;
v_x_758_ = v___x_774_;
goto _start;
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_769_);
lean_dec(v_tail_767_);
lean_dec(v_x_758_);
v_a_777_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_771_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_771_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg___boxed(lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_786_, v_x_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(lean_object* v_as_x27_794_, lean_object* v_b_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
if (lean_obj_tag(v_as_x27_794_) == 0)
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v_b_795_);
return v___x_801_;
}
else
{
lean_object* v_head_802_; lean_object* v_tail_803_; lean_object* v_a_805_; lean_object* v_a_809_; lean_object* v___x_2331__overap_815_; lean_object* v___x_816_; 
v_head_802_ = lean_ctor_get(v_as_x27_794_, 0);
v_tail_803_ = lean_ctor_get(v_as_x27_794_, 1);
lean_inc(v_head_802_);
v___x_2331__overap_815_ = lean_task_get_own(v_head_802_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
v___x_816_ = lean_apply_5(v___x_2331__overap_815_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, lean_box(0));
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref_known(v___x_816_, 1);
v___x_818_ = l_Lean_Meta_saveState___redArg(v___y_797_, v___y_799_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_a_817_);
lean_ctor_set(v___x_823_, 1, v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 1);
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
v_a_805_ = v___x_825_;
goto v___jp_804_;
}
}
}
else
{
lean_object* v_a_828_; 
lean_dec(v_a_817_);
v_a_828_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_818_, 1);
v_a_809_ = v_a_828_;
goto v___jp_808_;
}
}
else
{
lean_object* v_a_829_; 
v_a_829_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_816_, 1);
v_a_809_ = v_a_829_;
goto v___jp_808_;
}
v___jp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_806_, 0, v_a_805_);
lean_ctor_set(v___x_806_, 1, v_b_795_);
v_as_x27_794_ = v_tail_803_;
v_b_795_ = v___x_806_;
goto _start;
}
v___jp_808_:
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_Exception_isInterrupt(v_a_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; 
lean_inc_ref(v_a_809_);
v___x_811_ = l_Lean_Exception_isRuntime(v_a_809_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v_a_809_);
v_a_805_ = v___x_812_;
goto v___jp_804_;
}
else
{
lean_object* v___x_813_; 
lean_dec(v_b_795_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v_a_809_);
return v___x_813_;
}
}
else
{
lean_object* v___x_814_; 
lean_dec(v_b_795_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v_a_809_);
return v___x_814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg___boxed(lean_object* v_as_x27_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_830_, v_b_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v_as_x27_830_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg(lean_object* v_jobs_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = lean_st_ref_get(v_a_840_);
v___x_845_ = lean_box(0);
v___x_846_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_838_, v___x_845_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_a_847_, v___x_845_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_858_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_853_ = lean_st_ref_swap(v_a_840_, v___x_844_);
lean_dec(v___x_853_);
v___x_854_ = l_List_reverse___redArg(v_a_849_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_854_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_dec(v___x_844_);
return v___x_848_;
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v___x_844_);
v_a_859_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_846_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_846_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg___boxed(lean_object* v_jobs_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par(lean_object* v_00_u03b1_874_, lean_object* v_jobs_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___boxed(lean_object* v_00_u03b1_882_, lean_object* v_jobs_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Meta_MetaM_par(v_00_u03b1_882_, v_jobs_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(lean_object* v_00_u03b1_890_, lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_891_, v_x_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___boxed(lean_object* v_00_u03b1_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(v_00_u03b1_899_, v_x_900_, v_x_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(lean_object* v_00_u03b1_908_, lean_object* v_as_909_, lean_object* v_as_x27_910_, lean_object* v_b_911_, lean_object* v_a_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_910_, v_b_911_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___boxed(lean_object* v_00_u03b1_919_, lean_object* v_as_920_, lean_object* v_as_x27_921_, lean_object* v_b_922_, lean_object* v_a_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(v_00_u03b1_919_, v_as_920_, v_as_x27_921_, v_b_922_, v_a_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v_as_x27_921_);
lean_dec(v_as_920_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(lean_object* v_as_x27_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
if (lean_obj_tag(v_as_x27_930_) == 0)
{
lean_object* v___x_937_; 
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v_b_931_);
return v___x_937_;
}
else
{
lean_object* v_head_938_; lean_object* v_tail_939_; lean_object* v___x_2034__overap_940_; lean_object* v___x_941_; 
v_head_938_ = lean_ctor_get(v_as_x27_930_, 0);
v_tail_939_ = lean_ctor_get(v_as_x27_930_, 1);
lean_inc(v_head_938_);
v___x_2034__overap_940_ = lean_task_get_own(v_head_938_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
v___x_941_ = lean_apply_5(v___x_2034__overap_940_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, lean_box(0));
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_a_942_);
lean_dec_ref_known(v___x_941_, 1);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v_a_942_);
v___x_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_b_931_);
v_as_x27_930_ = v_tail_939_;
v_b_931_ = v___x_944_;
goto _start;
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_961_; 
v_a_946_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_961_ == 0)
{
v___x_948_ = v___x_941_;
v_isShared_949_ = v_isSharedCheck_961_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_941_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_961_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v___x_950_; 
v___x_950_ = l_Lean_Exception_isInterrupt(v_a_946_);
if (v___x_950_ == 0)
{
uint8_t v___x_951_; 
lean_inc(v_a_946_);
v___x_951_ = l_Lean_Exception_isRuntime(v_a_946_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_del_object(v___x_948_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v_a_946_);
v___x_953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set(v___x_953_, 1, v_b_931_);
v_as_x27_930_ = v_tail_939_;
v_b_931_ = v___x_953_;
goto _start;
}
else
{
lean_object* v___x_956_; 
lean_dec(v_b_931_);
if (v_isShared_949_ == 0)
{
v___x_956_ = v___x_948_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_946_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
lean_object* v___x_959_; 
lean_dec(v_b_931_);
if (v_isShared_949_ == 0)
{
v___x_959_ = v___x_948_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_946_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_962_, v_b_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_as_x27_962_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg(lean_object* v_jobs_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_976_ = lean_st_ref_get(v_a_972_);
v___x_977_ = lean_box(0);
v___x_978_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_970_, v___x_977_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_980_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_978_, 1);
v___x_980_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_a_979_, v___x_977_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec(v_a_979_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_990_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_990_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_990_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_985_ = lean_st_ref_swap(v_a_972_, v___x_976_);
lean_dec(v___x_985_);
v___x_986_ = l_List_reverse___redArg(v_a_981_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_986_);
v___x_988_ = v___x_983_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_dec(v___x_976_);
return v___x_980_;
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec(v___x_976_);
v_a_991_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_978_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_978_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg___boxed(lean_object* v_jobs_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27(lean_object* v_00_u03b1_1006_, lean_object* v_jobs_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_jobs_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_MetaM_par_x27(v_00_u03b1_1014_, v_jobs_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(lean_object* v_00_u03b1_1022_, lean_object* v_as_1023_, lean_object* v_as_x27_1024_, lean_object* v_b_1025_, lean_object* v_a_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_1024_, v_b_1025_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_1033_, lean_object* v_as_1034_, lean_object* v_as_x27_1035_, lean_object* v_b_1036_, lean_object* v_a_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(v_00_u03b1_1033_, v_as_1034_, v_as_x27_1035_, v_b_1036_, v_a_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v_as_x27_1035_);
lean_dec(v_as_1034_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
if (lean_obj_tag(v_x_1044_) == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = l_List_reverse___redArg(v_x_1045_);
v___x_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
else
{
lean_object* v_head_1053_; lean_object* v_tail_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1072_; 
v_head_1053_ = lean_ctor_get(v_x_1044_, 0);
v_tail_1054_ = lean_ctor_get(v_x_1044_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_1044_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1056_ = v_x_1044_;
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_tail_1054_);
lean_inc(v_head_1053_);
lean_dec(v_x_1044_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1072_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_MetaM_asTask___redArg(v_head_1053_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v_x_1045_);
lean_ctor_set(v___x_1056_, 0, v_a_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1059_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_x_1045_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
v_x_1044_ = v_tail_1054_;
v_x_1045_ = v___x_1061_;
goto _start;
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_del_object(v___x_1056_);
lean_dec(v_tail_1054_);
lean_dec(v_x_1045_);
v_a_1064_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_1058_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1058_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1073_, v_x_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg(lean_object* v_jobs_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = lean_box(0);
v___x_1088_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1081_, v___x_1087_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1107_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1107_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1107_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1106_; 
v___x_1093_ = l_List_unzipTR___redArg(v_a_1089_);
v_fst_1094_ = lean_ctor_get(v___x_1093_, 0);
v_snd_1095_ = lean_ctor_get(v___x_1093_, 1);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1097_ = v___x_1093_;
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_snd_1095_);
lean_inc(v_fst_1094_);
lean_dec(v___x_1093_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1099_, 0, v_fst_1094_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_snd_1095_);
v___x_1101_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1101_);
v___x_1103_ = v___x_1091_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1088_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1088_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel(lean_object* v_00_u03b1_1123_, lean_object* v_jobs_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_jobs_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Meta_MetaM_parIterWithCancel(v_00_u03b1_1131_, v_jobs_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1140_, v_x_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(v_00_u03b1_1148_, v_x_1149_, v_x_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg(lean_object* v_jobs_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_snd_1168_; lean_object* v___x_1170_; 
v_snd_1168_ = lean_ctor_get(v_a_1164_, 1);
lean_inc(v_snd_1168_);
lean_dec(v_a_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_snd_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_snd_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1163_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1163_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg___boxed(lean_object* v_jobs_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter(lean_object* v_00_u03b1_1188_, lean_object* v_jobs_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___boxed(lean_object* v_00_u03b1_1196_, lean_object* v_jobs_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Meta_MetaM_parIter(v_00_u03b1_1196_, v_jobs_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec_ref(v_a_1198_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_box(0);
v___x_1211_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1204_, v___x_1210_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1230_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1230_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1230_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v_fst_1217_; lean_object* v_snd_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1229_; 
v___x_1216_ = l_List_unzipTR___redArg(v_a_1212_);
v_fst_1217_ = lean_ctor_get(v___x_1216_, 0);
v_snd_1218_ = lean_ctor_get(v___x_1216_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1220_ = v___x_1216_;
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_snd_1218_);
lean_inc(v_fst_1217_);
lean_dec(v___x_1216_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1222_, 0, v_fst_1217_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_snd_1218_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1224_);
v___x_1226_ = v___x_1214_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
v_a_1231_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1211_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1211_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1246_, lean_object* v_jobs_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1254_, lean_object* v_jobs_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel(v_00_u03b1_1254_, v_jobs_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg(lean_object* v_jobs_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1277_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_snd_1273_; lean_object* v___x_1275_; 
v_snd_1273_ = lean_ctor_get(v_a_1269_, 1);
lean_inc(v_snd_1273_);
lean_dec(v_a_1269_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v_snd_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_snd_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
v_a_1278_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1268_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1268_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy(lean_object* v_00_u03b1_1293_, lean_object* v_jobs_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___boxed(lean_object* v_00_u03b1_1301_, lean_object* v_jobs_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_Meta_MetaM_parIterGreedy(v_00_u03b1_1301_, v_jobs_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_1309_, lean_object* v___x_1310_, lean_object* v_____r_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_a_1309_);
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1310_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_1321_, lean_object* v___x_1322_, lean_object* v_____r_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1321_, v___x_1322_, v_____r_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(uint8_t v_cancel_1330_, lean_object* v_fst_1331_, lean_object* v_a_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
if (lean_obj_tag(v_a_1332_) == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_fst_1331_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_b_1333_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___y_1346_; lean_object* v___x_1366_; 
lean_dec_ref(v_b_1333_);
v___x_1340_ = lean_box(0);
v___x_1341_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1342_ = l_IO_waitAny_x27___redArg(v_a_1332_);
v_fst_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_fst_1343_);
v_snd_1344_ = lean_ctor_get(v___x_1342_, 1);
lean_inc(v_snd_1344_);
lean_dec_ref(v___x_1342_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1366_ = lean_apply_5(v_fst_1343_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, lean_box(0));
if (lean_obj_tag(v___x_1366_) == 0)
{
if (v_cancel_1330_ == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1367_, v___x_1340_, v___x_1340_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
v___y_1346_ = v___x_1368_;
goto v___jp_1345_;
}
else
{
lean_object* v_a_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_a_1369_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1366_, 1);
lean_inc_ref(v_fst_1331_);
v___x_1370_ = lean_apply_1(v_fst_1331_, lean_box(0));
v___x_1371_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1369_, v___x_1340_, v___x_1370_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
v___y_1346_ = v___x_1371_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1385_; 
v_a_1372_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1374_ = v___x_1366_;
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1366_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
uint8_t v___x_1376_; 
v___x_1376_ = l_Lean_Exception_isInterrupt(v_a_1372_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
lean_inc(v_a_1372_);
v___x_1377_ = l_Lean_Exception_isRuntime(v_a_1372_);
if (v___x_1377_ == 0)
{
lean_del_object(v___x_1374_);
lean_dec(v_a_1372_);
v_a_1332_ = v_snd_1344_;
v_b_1333_ = v___x_1341_;
goto _start;
}
else
{
lean_object* v___x_1380_; 
lean_dec(v_snd_1344_);
lean_dec_ref(v_fst_1331_);
if (v_isShared_1375_ == 0)
{
v___x_1380_ = v___x_1374_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1372_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
lean_object* v___x_1383_; 
lean_dec(v_snd_1344_);
lean_dec_ref(v_fst_1331_);
if (v_isShared_1375_ == 0)
{
v___x_1383_ = v___x_1374_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1372_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
v___jp_1345_:
{
if (lean_obj_tag(v___y_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1357_; 
v_a_1347_ = lean_ctor_get(v___y_1346_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___y_1346_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1349_ = v___y_1346_;
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___y_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1357_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; 
lean_dec(v_snd_1344_);
lean_dec_ref(v_fst_1331_);
v_a_1351_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v_a_1347_, 1);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_a_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v_a_1355_; 
lean_del_object(v___x_1349_);
v_a_1355_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v_a_1347_, 1);
v_a_1332_ = v_snd_1344_;
v_b_1333_ = v_a_1355_;
goto _start;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_snd_1344_);
lean_dec_ref(v_fst_1331_);
v_a_1358_ = lean_ctor_get(v___y_1346_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___y_1346_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___y_1346_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___y_1346_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_1386_, lean_object* v_fst_1387_, lean_object* v_a_1388_, lean_object* v_b_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v_cancel_boxed_1395_; lean_object* v_res_1396_; 
v_cancel_boxed_1395_ = lean_unbox(v_cancel_1386_);
v_res_1396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_boxed_1395_, v_fst_1387_, v_a_1388_, v_b_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(lean_object* v_msgData_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v_env_1404_; uint8_t v___x_1405_; lean_object* v_env_1406_; lean_object* v___x_1407_; lean_object* v_toCold_1408_; lean_object* v_mctx_1409_; lean_object* v_lctx_1410_; lean_object* v_options_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1403_ = lean_st_ref_get(v___y_1401_);
v_env_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref(v_env_1404_);
lean_dec(v___x_1403_);
v___x_1405_ = 0;
v_env_1406_ = l_Lean_Environment_setRecordingDeps(v_env_1404_, v___x_1405_);
v___x_1407_ = lean_st_ref_get(v___y_1399_);
v_toCold_1408_ = lean_ctor_get(v___y_1400_, 0);
v_mctx_1409_ = lean_ctor_get(v___x_1407_, 0);
lean_inc_ref(v_mctx_1409_);
lean_dec(v___x_1407_);
v_lctx_1410_ = lean_ctor_get(v___y_1398_, 2);
v_options_1411_ = lean_ctor_get(v_toCold_1408_, 2);
lean_inc_ref(v_options_1411_);
lean_inc_ref(v_lctx_1410_);
v___x_1412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1412_, 0, v_env_1406_);
lean_ctor_set(v___x_1412_, 1, v_mctx_1409_);
lean_ctor_set(v___x_1412_, 2, v_lctx_1410_);
lean_ctor_set(v___x_1412_, 3, v_options_1411_);
v___x_1413_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v_msgData_1397_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msgData_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_ref_1428_; lean_object* v___x_1429_; lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1438_; 
v_ref_1428_ = lean_ctor_get(v___y_1425_, 2);
v___x_1429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_inc(v_ref_1428_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_ref_1428_);
lean_ctor_set(v___x_1434_, 1, v_a_1430_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set_tag(v___x_1432_, 1);
lean_ctor_set(v___x_1432_, 0, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg(lean_object* v_jobs_1446_, uint8_t v_cancel_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1446_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v_fst_1455_; lean_object* v_snd_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v_fst_1455_ = lean_ctor_get(v_a_1454_, 0);
lean_inc(v_fst_1455_);
v_snd_1456_ = lean_ctor_get(v_a_1454_, 1);
lean_inc(v_snd_1456_);
lean_dec(v_a_1454_);
v___x_1457_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1447_, v_fst_1455_, v_snd_1456_, v___x_1457_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1470_; 
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1470_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1470_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_fst_1463_; 
v_fst_1463_ = lean_ctor_get(v_a_1459_, 0);
lean_inc(v_fst_1463_);
lean_dec(v_a_1459_);
if (lean_obj_tag(v_fst_1463_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
lean_del_object(v___x_1461_);
v___x_1464_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_1465_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v___x_1464_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_);
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1468_; 
v_val_1466_ = lean_ctor_get(v_fst_1463_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_fst_1463_, 1);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v_val_1466_);
v___x_1468_ = v___x_1461_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_val_1466_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_a_1471_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1458_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1458_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
v_a_1479_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1453_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1453_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg___boxed(lean_object* v_jobs_1487_, lean_object* v_cancel_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
uint8_t v_cancel_boxed_1494_; lean_object* v_res_1495_; 
v_cancel_boxed_1494_ = lean_unbox(v_cancel_1488_);
v_res_1495_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1487_, v_cancel_boxed_1494_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst(lean_object* v_00_u03b1_1496_, lean_object* v_jobs_1497_, uint8_t v_cancel_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1497_, v_cancel_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___boxed(lean_object* v_00_u03b1_1505_, lean_object* v_jobs_1506_, lean_object* v_cancel_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
uint8_t v_cancel_boxed_1513_; lean_object* v_res_1514_; 
v_cancel_boxed_1513_ = lean_unbox(v_cancel_1507_);
v_res_1514_ = l_Lean_Meta_MetaM_parFirst(v_00_u03b1_1505_, v_jobs_1506_, v_cancel_boxed_1513_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(lean_object* v_00_u03b1_1515_, uint8_t v_cancel_1516_, lean_object* v_fst_1517_, lean_object* v_inst_1518_, lean_object* v_R_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v_c_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1516_, v_fst_1517_, v_a_1520_, v_b_1521_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_1529_, lean_object* v_cancel_1530_, lean_object* v_fst_1531_, lean_object* v_inst_1532_, lean_object* v_R_1533_, lean_object* v_a_1534_, lean_object* v_b_1535_, lean_object* v_c_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
uint8_t v_cancel_boxed_1542_; lean_object* v_res_1543_; 
v_cancel_boxed_1542_ = lean_unbox(v_cancel_1530_);
v_res_1543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(v_00_u03b1_1529_, v_cancel_boxed_1542_, v_fst_1531_, v_inst_1532_, v_R_1533_, v_a_1534_, v_b_1535_, v_c_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(lean_object* v_00_u03b1_1544_, lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_1552_, lean_object* v_msg_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(v_00_u03b1_1552_, v_msg_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
if (lean_obj_tag(v_x_1560_) == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = l_List_reverse___redArg(v_x_1561_);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
else
{
lean_object* v_head_1571_; lean_object* v_tail_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1590_; 
v_head_1571_ = lean_ctor_get(v_x_1560_, 0);
v_tail_1572_ = lean_ctor_get(v_x_1560_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_x_1560_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1574_ = v_x_1560_;
v_isShared_1575_ = v_isSharedCheck_1590_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_tail_1572_);
lean_inc(v_head_1571_);
lean_dec(v_x_1560_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1590_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_head_1571_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v___x_1576_, 1);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v_x_1561_);
lean_ctor_set(v___x_1574_, 0, v_a_1577_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1577_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_x_1561_);
v___x_1579_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v_x_1560_ = v_tail_1572_;
v_x_1561_ = v___x_1579_;
goto _start;
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_del_object(v___x_1574_);
lean_dec(v_tail_1572_);
lean_dec(v_x_1561_);
v_a_1582_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1576_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1576_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1591_, v_x_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(lean_object* v_jobs_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1601_, v___x_1609_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1629_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1629_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1629_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v_fst_1616_; lean_object* v_snd_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1628_; 
v___x_1615_ = l_List_unzipTR___redArg(v_a_1611_);
v_fst_1616_ = lean_ctor_get(v___x_1615_, 0);
v_snd_1617_ = lean_ctor_get(v___x_1615_, 1);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1619_ = v___x_1615_;
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_snd_1617_);
lean_inc(v_fst_1616_);
lean_dec(v___x_1615_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1628_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1621_, 0, v_fst_1616_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_snd_1617_);
v___x_1623_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1625_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1623_);
v___x_1625_ = v___x_1613_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
v_a_1630_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1610_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1610_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel(lean_object* v_00_u03b1_1647_, lean_object* v_jobs_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1657_, lean_object* v_jobs_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel(v_00_u03b1_1657_, v_jobs_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1668_, v_x_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(v_00_u03b1_1678_, v_x_1679_, v_x_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg(lean_object* v_jobs_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_snd_1702_; lean_object* v___x_1704_; 
v_snd_1702_ = lean_ctor_get(v_a_1698_, 1);
lean_inc(v_snd_1702_);
lean_dec(v_a_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v_snd_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_snd_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
v_a_1707_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1697_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg___boxed(lean_object* v_jobs_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter(lean_object* v_00_u03b1_1724_, lean_object* v_jobs_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_jobs_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Elab_Term_TermElabM_parIter(v_00_u03b1_1734_, v_jobs_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec_ref(v_a_1736_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_box(0);
v___x_1753_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1744_, v___x_1752_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1772_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1756_ = v___x_1753_;
v_isShared_1757_ = v_isSharedCheck_1772_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1772_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v_fst_1759_; lean_object* v_snd_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1771_; 
v___x_1758_ = l_List_unzipTR___redArg(v_a_1754_);
v_fst_1759_ = lean_ctor_get(v___x_1758_, 0);
v_snd_1760_ = lean_ctor_get(v___x_1758_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1762_ = v___x_1758_;
v_isShared_1763_ = v_isSharedCheck_1771_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_snd_1760_);
lean_inc(v_fst_1759_);
lean_dec(v___x_1758_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1771_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1764_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1764_, 0, v_fst_1759_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_snd_1760_);
v___x_1766_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1766_);
v___x_1768_ = v___x_1756_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
v_a_1773_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1753_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1753_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1790_, lean_object* v_jobs_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1800_, lean_object* v_jobs_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(v_00_u03b1_1800_, v_jobs_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(lean_object* v_jobs_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v_snd_1823_; lean_object* v___x_1825_; 
v_snd_1823_ = lean_ctor_get(v_a_1819_, 1);
lean_inc(v_snd_1823_);
lean_dec(v_a_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v_snd_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_snd_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1818_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1818_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec(v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy(lean_object* v_00_u03b1_1845_, lean_object* v_jobs_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___boxed(lean_object* v_00_u03b1_1855_, lean_object* v_jobs_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Elab_Term_TermElabM_parIterGreedy(v_00_u03b1_1855_, v_jobs_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = l_List_reverse___redArg(v_x_1866_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
else
{
lean_object* v_head_1876_; lean_object* v_tail_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1895_; 
v_head_1876_ = lean_ctor_get(v_x_1865_, 0);
v_tail_1877_ = lean_ctor_get(v_x_1865_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_x_1865_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1879_ = v_x_1865_;
v_isShared_1880_ = v_isSharedCheck_1895_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_tail_1877_);
lean_inc(v_head_1876_);
lean_dec(v_x_1865_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1895_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_head_1876_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v_x_1866_);
lean_ctor_set(v___x_1879_, 0, v_a_1882_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1882_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_x_1866_);
v___x_1884_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
v_x_1865_ = v_tail_1877_;
v_x_1866_ = v___x_1884_;
goto _start;
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_del_object(v___x_1879_);
lean_dec(v_tail_1877_);
lean_dec(v_x_1866_);
v_a_1887_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1881_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1881_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg___boxed(lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_1896_, v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(lean_object* v_as_x27_1906_, lean_object* v_b_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
if (lean_obj_tag(v_as_x27_1906_) == 0)
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_b_1907_);
return v___x_1915_;
}
else
{
lean_object* v_head_1916_; lean_object* v_tail_1917_; lean_object* v_a_1919_; lean_object* v___x_2956__overap_1927_; lean_object* v___x_1928_; 
v_head_1916_ = lean_ctor_get(v_as_x27_1906_, 0);
v_tail_1917_ = lean_ctor_get(v_as_x27_1906_, 1);
lean_inc(v_head_1916_);
v___x_2956__overap_1927_ = lean_task_get_own(v_head_1916_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
v___x_1928_ = lean_apply_7(v___x_2956__overap_1927_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, lean_box(0));
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
v___x_1930_ = l_Lean_Elab_Term_saveState___redArg(v___y_1909_, v___y_1911_, v___y_1913_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1941_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1941_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_a_1929_);
lean_ctor_set(v___x_1935_, 1, v_a_1931_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set_tag(v___x_1933_, 1);
lean_ctor_set(v___x_1933_, 0, v___x_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
lean_ctor_set(v___x_1938_, 1, v_b_1907_);
v_as_x27_1906_ = v_tail_1917_;
v_b_1907_ = v___x_1938_;
goto _start;
}
}
}
else
{
lean_object* v_a_1942_; 
lean_dec(v_a_1929_);
v_a_1942_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1930_, 1);
v_a_1919_ = v_a_1942_;
goto v___jp_1918_;
}
}
else
{
lean_object* v_a_1943_; 
v_a_1943_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1928_, 1);
v_a_1919_ = v_a_1943_;
goto v___jp_1918_;
}
v___jp_1918_:
{
uint8_t v___x_1920_; 
v___x_1920_ = l_Lean_Exception_isInterrupt(v_a_1919_);
if (v___x_1920_ == 0)
{
uint8_t v___x_1921_; 
lean_inc_ref(v_a_1919_);
v___x_1921_ = l_Lean_Exception_isRuntime(v_a_1919_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_a_1919_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_b_1907_);
v_as_x27_1906_ = v_tail_1917_;
v_b_1907_ = v___x_1923_;
goto _start;
}
else
{
lean_object* v___x_1925_; 
lean_dec(v_b_1907_);
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1919_);
return v___x_1925_;
}
}
else
{
lean_object* v___x_1926_; 
lean_dec(v_b_1907_);
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_a_1919_);
return v___x_1926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg___boxed(lean_object* v_as_x27_1944_, lean_object* v_b_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_1944_, v_b_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v_as_x27_1944_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg(lean_object* v_jobs_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_st_ref_get(v_a_1956_);
v___x_1963_ = lean_box(0);
v___x_1964_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_1954_, v___x_1963_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1966_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1964_, 1);
v___x_1966_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_a_1965_, v___x_1963_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
lean_dec(v_a_1965_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1976_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1976_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1976_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1971_ = lean_st_ref_swap(v_a_1956_, v___x_1962_);
lean_dec(v___x_1971_);
v___x_1972_ = l_List_reverse___redArg(v_a_1967_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1972_);
v___x_1974_ = v___x_1969_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
else
{
lean_dec(v___x_1962_);
return v___x_1966_;
}
}
else
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
lean_dec(v___x_1962_);
v_a_1977_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1964_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1964_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_a_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg___boxed(lean_object* v_jobs_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par(lean_object* v_00_u03b1_1994_, lean_object* v_jobs_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___boxed(lean_object* v_00_u03b1_2004_, lean_object* v_jobs_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lean_Elab_Term_TermElabM_par(v_00_u03b1_2004_, v_jobs_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(lean_object* v_00_u03b1_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_2015_, v_x_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___boxed(lean_object* v_00_u03b1_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(v_00_u03b1_2025_, v_x_2026_, v_x_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(lean_object* v_00_u03b1_2036_, lean_object* v_as_2037_, lean_object* v_as_x27_2038_, lean_object* v_b_2039_, lean_object* v_a_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_2038_, v_b_2039_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___boxed(lean_object* v_00_u03b1_2049_, lean_object* v_as_2050_, lean_object* v_as_x27_2051_, lean_object* v_b_2052_, lean_object* v_a_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(v_00_u03b1_2049_, v_as_2050_, v_as_x27_2051_, v_b_2052_, v_a_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v_as_x27_2051_);
lean_dec(v_as_2050_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(lean_object* v_as_x27_2062_, lean_object* v_b_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
if (lean_obj_tag(v_as_x27_2062_) == 0)
{
lean_object* v___x_2071_; 
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_b_2063_);
return v___x_2071_;
}
else
{
lean_object* v_head_2072_; lean_object* v_tail_2073_; lean_object* v___x_2566__overap_2074_; lean_object* v___x_2075_; 
v_head_2072_ = lean_ctor_get(v_as_x27_2062_, 0);
v_tail_2073_ = lean_ctor_get(v_as_x27_2062_, 1);
lean_inc(v_head_2072_);
v___x_2566__overap_2074_ = lean_task_get_own(v_head_2072_);
lean_inc(v___y_2069_);
lean_inc_ref(v___y_2068_);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2066_);
lean_inc(v___y_2065_);
lean_inc_ref(v___y_2064_);
v___x_2075_ = lean_apply_7(v___x_2566__overap_2074_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, lean_box(0));
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_a_2076_);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v_b_2063_);
v_as_x27_2062_ = v_tail_2073_;
v_b_2063_ = v___x_2078_;
goto _start;
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2095_; 
v_a_2080_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2082_ = v___x_2075_;
v_isShared_2083_ = v_isSharedCheck_2095_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2075_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2095_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint8_t v___x_2084_; 
v___x_2084_ = l_Lean_Exception_isInterrupt(v_a_2080_);
if (v___x_2084_ == 0)
{
uint8_t v___x_2085_; 
lean_inc(v_a_2080_);
v___x_2085_ = l_Lean_Exception_isRuntime(v_a_2080_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_del_object(v___x_2082_);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v_a_2080_);
v___x_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v_b_2063_);
v_as_x27_2062_ = v_tail_2073_;
v_b_2063_ = v___x_2087_;
goto _start;
}
else
{
lean_object* v___x_2090_; 
lean_dec(v_b_2063_);
if (v_isShared_2083_ == 0)
{
v___x_2090_ = v___x_2082_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2080_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
else
{
lean_object* v___x_2093_; 
lean_dec(v_b_2063_);
if (v_isShared_2083_ == 0)
{
v___x_2093_ = v___x_2082_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2080_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_2096_, lean_object* v_b_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2096_, v_b_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v_as_x27_2096_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg(lean_object* v_jobs_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_st_ref_get(v_a_2108_);
v___x_2115_ = lean_box(0);
v___x_2116_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_2106_, v___x_2115_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_a_2117_, v___x_2115_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec(v_a_2117_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2128_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2128_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_st_ref_swap(v_a_2108_, v___x_2114_);
lean_dec(v___x_2123_);
v___x_2124_ = l_List_reverse___redArg(v_a_2119_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
else
{
lean_dec(v___x_2114_);
return v___x_2118_;
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v___x_2114_);
v_a_2129_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2116_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2116_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg___boxed(lean_object* v_jobs_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27(lean_object* v_00_u03b1_2146_, lean_object* v_jobs_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___boxed(lean_object* v_00_u03b1_2156_, lean_object* v_jobs_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Elab_Term_TermElabM_par_x27(v_00_u03b1_2156_, v_jobs_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(lean_object* v_00_u03b1_2166_, lean_object* v_as_2167_, lean_object* v_as_x27_2168_, lean_object* v_b_2169_, lean_object* v_a_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2168_, v_b_2169_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_as_2180_, lean_object* v_as_x27_2181_, lean_object* v_b_2182_, lean_object* v_a_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(v_00_u03b1_2179_, v_as_2180_, v_as_x27_2181_, v_b_2182_, v_a_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v_as_x27_2181_);
lean_dec(v_as_2180_);
return v_res_2191_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_box(1);
v___x_2193_ = l_Lean_MessageData_ofFormat(v___x_2192_);
return v___x_2193_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2));
v___x_2198_ = l_Lean_MessageData_ofFormat(v___x_2197_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
if (lean_obj_tag(v_x_2200_) == 0)
{
return v_x_2199_;
}
else
{
lean_object* v_head_2201_; lean_object* v_tail_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2224_; 
v_head_2201_ = lean_ctor_get(v_x_2200_, 0);
v_tail_2202_ = lean_ctor_get(v_x_2200_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_x_2200_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2204_ = v_x_2200_;
v_isShared_2205_ = v_isSharedCheck_2224_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_tail_2202_);
lean_inc(v_head_2201_);
lean_dec(v_x_2200_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2224_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_before_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2222_; 
v_before_2206_ = lean_ctor_get(v_head_2201_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_head_2201_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v_head_2201_, 1);
lean_dec(v_unused_2223_);
v___x_2208_ = v_head_2201_;
v_isShared_2209_ = v_isSharedCheck_2222_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_before_2206_);
lean_dec(v_head_2201_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2222_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2209_ == 0)
{
lean_ctor_set_tag(v___x_2208_, 7);
lean_ctor_set(v___x_2208_, 1, v___x_2210_);
lean_ctor_set(v___x_2208_, 0, v_x_2199_);
v___x_2212_ = v___x_2208_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_x_2199_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_2205_ == 0)
{
lean_ctor_set_tag(v___x_2204_, 7);
lean_ctor_set(v___x_2204_, 1, v___x_2213_);
lean_ctor_set(v___x_2204_, 0, v___x_2212_);
v___x_2215_ = v___x_2204_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = l_Lean_MessageData_ofSyntax(v_before_2206_);
v___x_2217_ = l_Lean_indentD(v___x_2216_);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2215_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v_x_2199_ = v___x_2218_;
v_x_2200_ = v_tail_2202_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(lean_object* v_opts_2225_, lean_object* v_opt_2226_){
_start:
{
lean_object* v_name_2227_; lean_object* v_defValue_2228_; lean_object* v_map_2229_; lean_object* v___x_2230_; 
v_name_2227_ = lean_ctor_get(v_opt_2226_, 0);
v_defValue_2228_ = lean_ctor_get(v_opt_2226_, 1);
v_map_2229_ = lean_ctor_get(v_opts_2225_, 0);
v___x_2230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2229_, v_name_2227_);
if (lean_obj_tag(v___x_2230_) == 0)
{
uint8_t v___x_2231_; 
v___x_2231_ = lean_unbox(v_defValue_2228_);
return v___x_2231_;
}
else
{
lean_object* v_val_2232_; 
v_val_2232_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2232_);
lean_dec_ref_known(v___x_2230_, 1);
if (lean_obj_tag(v_val_2232_) == 1)
{
uint8_t v_v_2233_; 
v_v_2233_ = lean_ctor_get_uint8(v_val_2232_, 0);
lean_dec_ref_known(v_val_2232_, 0);
return v_v_2233_;
}
else
{
uint8_t v___x_2234_; 
lean_dec(v_val_2232_);
v___x_2234_ = lean_unbox(v_defValue_2228_);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2___boxed(lean_object* v_opts_2235_, lean_object* v_opt_2236_){
_start:
{
uint8_t v_res_2237_; lean_object* v_r_2238_; 
v_res_2237_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_opts_2235_, v_opt_2236_);
lean_dec_ref(v_opt_2236_);
lean_dec_ref(v_opts_2235_);
v_r_2238_ = lean_box(v_res_2237_);
return v_r_2238_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1));
v___x_2243_ = l_Lean_MessageData_ofFormat(v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(lean_object* v_msgData_2244_, lean_object* v_macroStack_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2248_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2246_);
v___x_2249_ = l_Lean_Elab_pp_macroStack;
v___x_2250_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v___x_2248_, v___x_2249_);
lean_dec_ref(v___x_2248_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; 
lean_dec(v_macroStack_2245_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v_msgData_2244_);
return v___x_2251_;
}
else
{
if (lean_obj_tag(v_macroStack_2245_) == 0)
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_msgData_2244_);
return v___x_2252_;
}
else
{
lean_object* v_head_2253_; lean_object* v_after_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2269_; 
v_head_2253_ = lean_ctor_get(v_macroStack_2245_, 0);
lean_inc(v_head_2253_);
v_after_2254_ = lean_ctor_get(v_head_2253_, 1);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_head_2253_);
if (v_isSharedCheck_2269_ == 0)
{
lean_object* v_unused_2270_; 
v_unused_2270_ = lean_ctor_get(v_head_2253_, 0);
lean_dec(v_unused_2270_);
v___x_2256_ = v_head_2253_;
v_isShared_2257_ = v_isSharedCheck_2269_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_after_2254_);
lean_dec(v_head_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2269_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2257_ == 0)
{
lean_ctor_set_tag(v___x_2256_, 7);
lean_ctor_set(v___x_2256_, 1, v___x_2258_);
lean_ctor_set(v___x_2256_, 0, v_msgData_2244_);
v___x_2260_ = v___x_2256_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_msgData_2244_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_msgData_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2261_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2);
v___x_2262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2260_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_MessageData_ofSyntax(v_after_2254_);
v___x_2264_ = l_Lean_indentD(v___x_2263_);
v_msgData_2265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2265_, 0, v___x_2262_);
lean_ctor_set(v_msgData_2265_, 1, v___x_2264_);
v___x_2266_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(v_msgData_2265_, v_macroStack_2245_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2271_, lean_object* v_macroStack_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2271_, v_macroStack_2272_, v___y_2273_);
lean_dec_ref(v___y_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(lean_object* v_msg_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_ref_2284_; lean_object* v_macroStack_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2298_; 
v_ref_2284_ = lean_ctor_get(v___y_2281_, 2);
v_macroStack_2285_ = lean_ctor_get(v___y_2277_, 1);
v___x_2286_ = l_Lean_Elab_getBetterRef(v_ref_2284_, v_macroStack_2285_);
v___x_2287_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_2276_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2287_);
lean_inc(v_macroStack_2285_);
v___x_2289_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_a_2288_, v_macroStack_2285_, v___y_2281_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2286_);
lean_ctor_set(v___x_2294_, 1, v_a_2290_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set_tag(v___x_2292_, 1);
lean_ctor_set(v___x_2292_, 0, v___x_2294_);
v___x_2296_ = v___x_2292_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_2308_, lean_object* v___x_2309_, lean_object* v_____r_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_a_2308_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v___x_2309_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_2322_, lean_object* v___x_2323_, lean_object* v_____r_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2322_, v___x_2323_, v_____r_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(uint8_t v_cancel_2333_, lean_object* v_fst_2334_, lean_object* v_a_2335_, lean_object* v_b_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
if (lean_obj_tag(v_a_2335_) == 0)
{
lean_object* v___x_2344_; 
lean_dec_ref(v_fst_2334_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_b_2336_);
return v___x_2344_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v_fst_2348_; lean_object* v_snd_2349_; lean_object* v___y_2351_; lean_object* v___x_2371_; 
lean_dec_ref(v_b_2336_);
v___x_2345_ = lean_box(0);
v___x_2346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2347_ = l_IO_waitAny_x27___redArg(v_a_2335_);
v_fst_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_fst_2348_);
v_snd_2349_ = lean_ctor_get(v___x_2347_, 1);
lean_inc(v_snd_2349_);
lean_dec_ref(v___x_2347_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
lean_inc(v___y_2338_);
lean_inc_ref(v___y_2337_);
v___x_2371_ = lean_apply_7(v_fst_2348_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, lean_box(0));
if (lean_obj_tag(v___x_2371_) == 0)
{
if (v_cancel_2333_ == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2373_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2373_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2372_, v___x_2345_, v___x_2345_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
v___y_2351_ = v___x_2373_;
goto v___jp_2350_;
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_a_2374_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2371_, 1);
lean_inc_ref(v_fst_2334_);
v___x_2375_ = lean_apply_1(v_fst_2334_, lean_box(0));
v___x_2376_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2374_, v___x_2345_, v___x_2375_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
v___y_2351_ = v___x_2376_;
goto v___jp_2350_;
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2390_; 
v_a_2377_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2379_ = v___x_2371_;
v_isShared_2380_ = v_isSharedCheck_2390_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2371_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2390_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
uint8_t v___x_2381_; 
v___x_2381_ = l_Lean_Exception_isInterrupt(v_a_2377_);
if (v___x_2381_ == 0)
{
uint8_t v___x_2382_; 
lean_inc(v_a_2377_);
v___x_2382_ = l_Lean_Exception_isRuntime(v_a_2377_);
if (v___x_2382_ == 0)
{
lean_del_object(v___x_2379_);
lean_dec(v_a_2377_);
v_a_2335_ = v_snd_2349_;
v_b_2336_ = v___x_2346_;
goto _start;
}
else
{
lean_object* v___x_2385_; 
lean_dec(v_snd_2349_);
lean_dec_ref(v_fst_2334_);
if (v_isShared_2380_ == 0)
{
v___x_2385_ = v___x_2379_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2377_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
else
{
lean_object* v___x_2388_; 
lean_dec(v_snd_2349_);
lean_dec_ref(v_fst_2334_);
if (v_isShared_2380_ == 0)
{
v___x_2388_ = v___x_2379_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2377_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
v___jp_2350_:
{
if (lean_obj_tag(v___y_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2362_; 
v_a_2352_ = lean_ctor_get(v___y_2351_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___y_2351_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2354_ = v___y_2351_;
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___y_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2362_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
if (lean_obj_tag(v_a_2352_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; 
lean_dec(v_snd_2349_);
lean_dec_ref(v_fst_2334_);
v_a_2356_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v_a_2352_, 1);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v_a_2356_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
else
{
lean_object* v_a_2360_; 
lean_del_object(v___x_2354_);
v_a_2360_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v_a_2352_, 1);
v_a_2335_ = v_snd_2349_;
v_b_2336_ = v_a_2360_;
goto _start;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec(v_snd_2349_);
lean_dec_ref(v_fst_2334_);
v_a_2363_ = lean_ctor_get(v___y_2351_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___y_2351_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___y_2351_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___y_2351_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_2391_, lean_object* v_fst_2392_, lean_object* v_a_2393_, lean_object* v_b_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
uint8_t v_cancel_boxed_2402_; lean_object* v_res_2403_; 
v_cancel_boxed_2402_ = lean_unbox(v_cancel_2391_);
v_res_2403_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_boxed_2402_, v_fst_2392_, v_a_2393_, v_b_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg(lean_object* v_jobs_2404_, uint8_t v_cancel_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_2404_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v_fst_2415_ = lean_ctor_get(v_a_2414_, 0);
lean_inc(v_fst_2415_);
v_snd_2416_ = lean_ctor_get(v_a_2414_, 1);
lean_inc(v_snd_2416_);
lean_dec(v_a_2414_);
v___x_2417_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2418_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2405_, v_fst_2415_, v_snd_2416_, v___x_2417_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2430_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2421_ = v___x_2418_;
v_isShared_2422_ = v_isSharedCheck_2430_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2418_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2430_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_fst_2423_; 
v_fst_2423_ = lean_ctor_get(v_a_2419_, 0);
lean_inc(v_fst_2423_);
lean_dec(v_a_2419_);
if (lean_obj_tag(v_fst_2423_) == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_del_object(v___x_2421_);
v___x_2424_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_2425_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v___x_2424_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
return v___x_2425_;
}
else
{
lean_object* v_val_2426_; lean_object* v___x_2428_; 
v_val_2426_ = lean_ctor_get(v_fst_2423_, 0);
lean_inc(v_val_2426_);
lean_dec_ref_known(v_fst_2423_, 1);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_val_2426_);
v___x_2428_ = v___x_2421_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_val_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
v_a_2431_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2418_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2418_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_a_2439_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2413_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2413_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg___boxed(lean_object* v_jobs_2447_, lean_object* v_cancel_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_){
_start:
{
uint8_t v_cancel_boxed_2456_; lean_object* v_res_2457_; 
v_cancel_boxed_2456_ = lean_unbox(v_cancel_2448_);
v_res_2457_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2447_, v_cancel_boxed_2456_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
lean_dec(v_a_2454_);
lean_dec_ref(v_a_2453_);
lean_dec(v_a_2452_);
lean_dec_ref(v_a_2451_);
lean_dec(v_a_2450_);
lean_dec_ref(v_a_2449_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst(lean_object* v_00_u03b1_2458_, lean_object* v_jobs_2459_, uint8_t v_cancel_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2459_, v_cancel_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_jobs_2470_, lean_object* v_cancel_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
uint8_t v_cancel_boxed_2479_; lean_object* v_res_2480_; 
v_cancel_boxed_2479_ = lean_unbox(v_cancel_2471_);
v_res_2480_ = l_Lean_Elab_Term_TermElabM_parFirst(v_00_u03b1_2469_, v_jobs_2470_, v_cancel_boxed_2479_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(lean_object* v_00_u03b1_2481_, uint8_t v_cancel_2482_, lean_object* v_fst_2483_, lean_object* v_inst_2484_, lean_object* v_R_2485_, lean_object* v_a_2486_, lean_object* v_b_2487_, lean_object* v_c_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2482_, v_fst_2483_, v_a_2486_, v_b_2487_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_2497_, lean_object* v_cancel_2498_, lean_object* v_fst_2499_, lean_object* v_inst_2500_, lean_object* v_R_2501_, lean_object* v_a_2502_, lean_object* v_b_2503_, lean_object* v_c_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v_cancel_boxed_2512_; lean_object* v_res_2513_; 
v_cancel_boxed_2512_ = lean_unbox(v_cancel_2498_);
v_res_2513_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(v_00_u03b1_2497_, v_cancel_boxed_2512_, v_fst_2499_, v_inst_2500_, v_R_2501_, v_a_2502_, v_b_2503_, v_c_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(lean_object* v_00_u03b1_2514_, lean_object* v_msg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_2524_, lean_object* v_msg_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(v_00_u03b1_2524_, v_msg_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(lean_object* v_msgData_2534_, lean_object* v_macroStack_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2534_, v_macroStack_2535_, v___y_2540_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_2544_, lean_object* v_macroStack_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(v_msgData_2544_, v_macroStack_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(lean_object* v_x_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
if (lean_obj_tag(v_x_2554_) == 0)
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = l_List_reverse___redArg(v_x_2555_);
v___x_2566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
return v___x_2566_;
}
else
{
lean_object* v_head_2567_; lean_object* v_tail_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2586_; 
v_head_2567_ = lean_ctor_get(v_x_2554_, 0);
v_tail_2568_ = lean_ctor_get(v_x_2554_, 1);
v_isSharedCheck_2586_ = !lean_is_exclusive(v_x_2554_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2570_ = v_x_2554_;
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_tail_2568_);
lean_inc(v_head_2567_);
lean_dec(v_x_2554_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_head_2567_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2575_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v_x_2555_);
lean_ctor_set(v___x_2570_, 0, v_a_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2573_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_x_2555_);
v___x_2575_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
v_x_2554_ = v_tail_2568_;
v_x_2555_ = v___x_2575_;
goto _start;
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_del_object(v___x_2570_);
lean_dec(v_tail_2568_);
lean_dec(v_x_2555_);
v_a_2578_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2572_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2572_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_2587_, lean_object* v_x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2587_, v_x_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(lean_object* v_jobs_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_box(0);
v___x_2610_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2599_, v___x_2609_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2629_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2629_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2629_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2628_; 
v___x_2615_ = l_List_unzipTR___redArg(v_a_2611_);
v_fst_2616_ = lean_ctor_get(v___x_2615_, 0);
v_snd_2617_ = lean_ctor_get(v___x_2615_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2619_ = v___x_2615_;
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2617_);
lean_inc(v_fst_2616_);
lean_dec(v___x_2615_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2628_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2621_, 0, v_fst_2616_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2621_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_snd_2617_);
v___x_2623_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2625_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v___x_2623_);
v___x_2625_ = v___x_2613_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2637_; 
v_a_2630_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2632_ = v___x_2610_;
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_a_2630_);
lean_dec(v___x_2610_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2637_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2635_; 
if (v_isShared_2633_ == 0)
{
v___x_2635_ = v___x_2632_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_a_2630_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
lean_dec(v_a_2646_);
lean_dec_ref(v_a_2645_);
lean_dec(v_a_2644_);
lean_dec_ref(v_a_2643_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel(lean_object* v_00_u03b1_2649_, lean_object* v_jobs_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___boxed(lean_object* v_00_u03b1_2661_, lean_object* v_jobs_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel(v_00_u03b1_2661_, v_jobs_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2674_, v_x_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(v_00_u03b1_2686_, v_x_2687_, v_x_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg(lean_object* v_jobs_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2718_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2718_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_snd_2714_; lean_object* v___x_2716_; 
v_snd_2714_ = lean_ctor_get(v_a_2710_, 1);
lean_inc(v_snd_2714_);
lean_dec(v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v_snd_2714_);
v___x_2716_ = v___x_2712_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_snd_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
v_a_2719_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2709_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2709_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg___boxed(lean_object* v_jobs_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter(lean_object* v_00_u03b1_2738_, lean_object* v_jobs_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___boxed(lean_object* v_00_u03b1_2750_, lean_object* v_jobs_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Elab_Tactic_TacticM_parIter(v_00_u03b1_2750_, v_jobs_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2762_, v___x_2772_, v_a_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2792_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2776_ = v___x_2773_;
v_isShared_2777_ = v_isSharedCheck_2792_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2773_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2792_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v_fst_2779_; lean_object* v_snd_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2791_; 
v___x_2778_ = l_List_unzipTR___redArg(v_a_2774_);
v_fst_2779_ = lean_ctor_get(v___x_2778_, 0);
v_snd_2780_ = lean_ctor_get(v___x_2778_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2782_ = v___x_2778_;
v_isShared_2783_ = v_isSharedCheck_2791_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_snd_2780_);
lean_inc(v_fst_2779_);
lean_dec(v___x_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2791_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2784_, 0, v_fst_2779_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_snd_2780_);
v___x_2786_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2788_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2786_);
v___x_2788_ = v___x_2776_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
v_a_2793_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2773_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2773_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(lean_object* v_00_u03b1_2812_, lean_object* v_jobs_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_jobs_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(v_00_u03b1_2824_, v_jobs_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(lean_object* v_jobs_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2855_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2849_ = v___x_2846_;
v_isShared_2850_ = v_isSharedCheck_2855_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2846_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2855_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v_snd_2851_; lean_object* v___x_2853_; 
v_snd_2851_ = lean_ctor_get(v_a_2847_, 1);
lean_inc(v_snd_2851_);
lean_dec(v_a_2847_);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 0, v_snd_2851_);
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_snd_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
v_a_2856_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2846_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2846_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg___boxed(lean_object* v_jobs_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
lean_dec(v_a_2870_);
lean_dec_ref(v_a_2869_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy(lean_object* v_00_u03b1_2875_, lean_object* v_jobs_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___boxed(lean_object* v_00_u03b1_2887_, lean_object* v_jobs_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy(v_00_u03b1_2887_, v_jobs_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(lean_object* v_as_x27_2899_, lean_object* v_b_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
if (lean_obj_tag(v_as_x27_2899_) == 0)
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v_b_2900_);
return v___x_2910_;
}
else
{
lean_object* v_head_2911_; lean_object* v_tail_2912_; lean_object* v___x_2913_; 
v_head_2911_ = lean_ctor_get(v_as_x27_2899_, 0);
v_tail_2912_ = lean_ctor_get(v_as_x27_2899_, 1);
v___x_2913_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2902_, v___y_2904_, v___y_2906_, v___y_2908_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2957_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2957_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2957_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_a_2919_; lean_object* v___x_2660__overap_2940_; lean_object* v___x_2941_; 
lean_inc(v_head_2911_);
v___x_2660__overap_2940_ = lean_task_get_own(v_head_2911_);
lean_inc(v___y_2908_);
lean_inc_ref(v___y_2907_);
lean_inc(v___y_2906_);
lean_inc_ref(v___y_2905_);
lean_inc(v___y_2904_);
lean_inc_ref(v___y_2903_);
lean_inc(v___y_2902_);
lean_inc_ref(v___y_2901_);
v___x_2941_ = lean_apply_9(v___x_2660__overap_2940_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, lean_box(0));
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2902_, v___y_2904_, v___y_2906_, v___y_2908_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2954_; 
lean_del_object(v___x_2916_);
lean_dec(v_a_2914_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_2954_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2954_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2948_, 0, v_a_2942_);
lean_ctor_set(v___x_2948_, 1, v_a_2944_);
if (v_isShared_2947_ == 0)
{
lean_ctor_set_tag(v___x_2946_, 1);
lean_ctor_set(v___x_2946_, 0, v___x_2948_);
v___x_2950_ = v___x_2946_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; 
v___x_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2950_);
lean_ctor_set(v___x_2951_, 1, v_b_2900_);
v_as_x27_2899_ = v_tail_2912_;
v_b_2900_ = v___x_2951_;
goto _start;
}
}
}
else
{
lean_object* v_a_2955_; 
lean_dec(v_a_2942_);
v_a_2955_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2943_, 1);
v_a_2919_ = v_a_2955_;
goto v___jp_2918_;
}
}
else
{
lean_object* v_a_2956_; 
v_a_2956_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2941_, 1);
v_a_2919_ = v_a_2956_;
goto v___jp_2918_;
}
v___jp_2918_:
{
uint8_t v___x_2920_; 
v___x_2920_ = l_Lean_Exception_isInterrupt(v_a_2919_);
if (v___x_2920_ == 0)
{
uint8_t v___x_2921_; 
lean_inc_ref(v_a_2919_);
v___x_2921_ = l_Lean_Exception_isRuntime(v_a_2919_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; 
lean_del_object(v___x_2916_);
v___x_2922_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2914_, v___x_2921_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec_ref_known(v___x_2922_, 1);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_a_2919_);
v___x_2924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v_b_2900_);
v_as_x27_2899_ = v_tail_2912_;
v_b_2900_ = v___x_2924_;
goto _start;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v_a_2919_);
lean_dec(v_b_2900_);
v_a_2926_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2922_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2922_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v___x_2935_; 
lean_dec(v_a_2914_);
lean_dec(v_b_2900_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set_tag(v___x_2916_, 1);
lean_ctor_set(v___x_2916_, 0, v_a_2919_);
v___x_2935_ = v___x_2916_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2919_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_object* v___x_2938_; 
lean_dec(v_a_2914_);
lean_dec(v_b_2900_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set_tag(v___x_2916_, 1);
lean_ctor_set(v___x_2916_, 0, v_a_2919_);
v___x_2938_ = v___x_2916_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2919_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec(v_b_2900_);
v_a_2958_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2913_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2913_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg___boxed(lean_object* v_as_x27_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_2966_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v_as_x27_2966_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(lean_object* v_x_2978_, lean_object* v_x_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
if (lean_obj_tag(v_x_2978_) == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = l_List_reverse___redArg(v_x_2979_);
v___x_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2989_);
return v___x_2990_;
}
else
{
lean_object* v_head_2991_; lean_object* v_tail_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3010_; 
v_head_2991_ = lean_ctor_get(v_x_2978_, 0);
v_tail_2992_ = lean_ctor_get(v_x_2978_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_x_2978_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2994_ = v_x_2978_;
v_isShared_2995_ = v_isSharedCheck_3010_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_tail_2992_);
lean_inc(v_head_2991_);
lean_dec(v_x_2978_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3010_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_head_2991_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v_x_2979_);
lean_ctor_set(v___x_2994_, 0, v_a_2997_);
v___x_2999_ = v___x_2994_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2997_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_x_2979_);
v___x_2999_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
v_x_2978_ = v_tail_2992_;
v_x_2979_ = v___x_2999_;
goto _start;
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_del_object(v___x_2994_);
lean_dec(v_tail_2992_);
lean_dec(v_x_2979_);
v_a_3002_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2996_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2996_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg___boxed(lean_object* v_x_3011_, lean_object* v_x_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3011_, v_x_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg(lean_object* v_jobs_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_st_ref_get(v_a_3025_);
v___x_3034_ = lean_box(0);
v___x_3035_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_jobs_3023_, v___x_3034_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_a_3036_, v___x_3034_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3047_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3047_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3047_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3042_ = lean_st_ref_swap(v_a_3025_, v___x_3033_);
lean_dec(v___x_3042_);
v___x_3043_ = l_List_reverse___redArg(v_a_3038_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3043_);
v___x_3045_ = v___x_3040_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
lean_dec(v___x_3033_);
return v___x_3037_;
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v___x_3033_);
v_a_3048_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3035_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3035_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg___boxed(lean_object* v_jobs_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par(lean_object* v_00_u03b1_3067_, lean_object* v_jobs_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___boxed(lean_object* v_00_u03b1_3079_, lean_object* v_jobs_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_Lean_Elab_Tactic_TacticM_par(v_00_u03b1_3079_, v_jobs_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_a_3087_);
lean_dec(v_a_3086_);
lean_dec_ref(v_a_3085_);
lean_dec(v_a_3084_);
lean_dec_ref(v_a_3083_);
lean_dec(v_a_3082_);
lean_dec_ref(v_a_3081_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(lean_object* v_00_u03b1_3091_, lean_object* v_x_3092_, lean_object* v_x_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3092_, v_x_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___boxed(lean_object* v_00_u03b1_3104_, lean_object* v_x_3105_, lean_object* v_x_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(v_00_u03b1_3104_, v_x_3105_, v_x_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(lean_object* v_00_u03b1_3117_, lean_object* v_as_3118_, lean_object* v_as_x27_3119_, lean_object* v_b_3120_, lean_object* v_a_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_3119_, v_b_3120_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_as_3133_, lean_object* v_as_x27_3134_, lean_object* v_b_3135_, lean_object* v_a_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(v_00_u03b1_3132_, v_as_3133_, v_as_x27_3134_, v_b_3135_, v_a_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec_ref(v___y_3141_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v_as_x27_3134_);
lean_dec(v_as_3133_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(lean_object* v_as_x27_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
if (lean_obj_tag(v_as_x27_3147_) == 0)
{
lean_object* v___x_3158_; 
v___x_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_b_3148_);
return v___x_3158_;
}
else
{
lean_object* v_head_3159_; lean_object* v_tail_3160_; lean_object* v___x_3161_; 
v_head_3159_ = lean_ctor_get(v_as_x27_3147_, 0);
v_tail_3160_ = lean_ctor_get(v_as_x27_3147_, 1);
v___x_3161_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3150_, v___y_3152_, v___y_3154_, v___y_3156_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_2345__overap_3163_; lean_object* v___x_3164_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
lean_inc(v_head_3159_);
v___x_2345__overap_3163_ = lean_task_get_own(v_head_3159_);
lean_inc(v___y_3156_);
lean_inc_ref(v___y_3155_);
lean_inc(v___y_3154_);
lean_inc_ref(v___y_3153_);
lean_inc(v___y_3152_);
lean_inc_ref(v___y_3151_);
lean_inc(v___y_3150_);
lean_inc_ref(v___y_3149_);
v___x_3164_ = lean_apply_9(v___x_2345__overap_3163_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, lean_box(0));
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec(v_a_3162_);
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref_known(v___x_3164_, 1);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_a_3165_);
v___x_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v_b_3148_);
v_as_x27_3147_ = v_tail_3160_;
v_b_3148_ = v___x_3167_;
goto _start;
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3193_; 
v_a_3169_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3171_ = v___x_3164_;
v_isShared_3172_ = v_isSharedCheck_3193_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3164_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3193_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
uint8_t v___x_3173_; 
v___x_3173_ = l_Lean_Exception_isInterrupt(v_a_3169_);
if (v___x_3173_ == 0)
{
uint8_t v___x_3174_; 
lean_inc(v_a_3169_);
v___x_3174_ = l_Lean_Exception_isRuntime(v_a_3169_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_del_object(v___x_3171_);
v___x_3175_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3162_, v___x_3174_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec_ref_known(v___x_3175_, 1);
v___x_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3176_, 0, v_a_3169_);
v___x_3177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v_b_3148_);
v_as_x27_3147_ = v_tail_3160_;
v_b_3148_ = v___x_3177_;
goto _start;
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v_a_3169_);
lean_dec(v_b_3148_);
v_a_3179_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3175_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3175_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v___x_3188_; 
lean_dec(v_a_3162_);
lean_dec(v_b_3148_);
if (v_isShared_3172_ == 0)
{
v___x_3188_ = v___x_3171_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3169_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
else
{
lean_object* v___x_3191_; 
lean_dec(v_a_3162_);
lean_dec(v_b_3148_);
if (v_isShared_3172_ == 0)
{
v___x_3191_ = v___x_3171_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3169_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v_b_3148_);
v_a_3194_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3161_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3161_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_3202_, lean_object* v_b_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_as_x27_3202_, v_b_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v_as_x27_3202_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg(lean_object* v_jobs_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3224_ = lean_st_ref_get(v_a_3216_);
v___x_3225_ = lean_box(0);
v___x_3226_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_jobs_3214_, v___x_3225_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; lean_object* v___x_3228_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_a_3227_, v___x_3225_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
lean_dec(v_a_3227_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3238_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3238_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3236_; 
v___x_3233_ = lean_st_ref_swap(v_a_3216_, v___x_3224_);
lean_dec(v___x_3233_);
v___x_3234_ = l_List_reverse___redArg(v_a_3229_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
else
{
lean_dec(v___x_3224_);
return v___x_3228_;
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v___x_3224_);
v_a_3239_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3226_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3226_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg___boxed(lean_object* v_jobs_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(v_jobs_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
lean_dec(v_a_3255_);
lean_dec_ref(v_a_3254_);
lean_dec(v_a_3253_);
lean_dec_ref(v_a_3252_);
lean_dec(v_a_3251_);
lean_dec_ref(v_a_3250_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27(lean_object* v_00_u03b1_3258_, lean_object* v_jobs_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(v_jobs_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___boxed(lean_object* v_00_u03b1_3270_, lean_object* v_jobs_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_Elab_Tactic_TacticM_par_x27(v_00_u03b1_3270_, v_jobs_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_);
lean_dec(v_a_3279_);
lean_dec_ref(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(lean_object* v_00_u03b1_3282_, lean_object* v_as_3283_, lean_object* v_as_x27_3284_, lean_object* v_b_3285_, lean_object* v_a_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_as_x27_3284_, v_b_3285_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_3297_, lean_object* v_as_3298_, lean_object* v_as_x27_3299_, lean_object* v_b_3300_, lean_object* v_a_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(v_00_u03b1_3297_, v_as_3298_, v_as_x27_3299_, v_b_3300_, v_a_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v_as_x27_3299_);
lean_dec(v_as_3298_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_3312_, lean_object* v___x_3313_, lean_object* v_____r_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3324_, 0, v_a_3312_);
v___x_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___x_3313_);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_3328_, lean_object* v___x_3329_, lean_object* v_____r_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3328_, v___x_3329_, v_____r_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(uint8_t v_cancel_3341_, lean_object* v_fst_3342_, lean_object* v_a_3343_, lean_object* v_b_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
if (lean_obj_tag(v_a_3343_) == 0)
{
lean_object* v___x_3354_; 
lean_dec_ref(v_fst_3342_);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_b_3344_);
return v___x_3354_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v___y_3361_; lean_object* v___x_3381_; 
lean_dec_ref(v_b_3344_);
v___x_3355_ = lean_box(0);
v___x_3356_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_3357_ = l_IO_waitAny_x27___redArg(v_a_3343_);
v_fst_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_fst_3358_);
v_snd_3359_ = lean_ctor_get(v___x_3357_, 1);
lean_inc(v_snd_3359_);
lean_dec_ref(v___x_3357_);
v___x_3381_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3346_, v___y_3348_, v___y_3350_, v___y_3352_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
lean_inc(v___y_3352_);
lean_inc_ref(v___y_3351_);
lean_inc(v___y_3350_);
lean_inc_ref(v___y_3349_);
lean_inc(v___y_3348_);
lean_inc_ref(v___y_3347_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
v___x_3383_ = lean_apply_9(v_fst_3358_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, lean_box(0));
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_dec(v_a_3382_);
if (v_cancel_3341_ == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3385_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___x_3385_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3384_, v___x_3355_, v___x_3355_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
v___y_3361_ = v___x_3385_;
goto v___jp_3360_;
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_a_3386_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3383_, 1);
lean_inc_ref(v_fst_3342_);
v___x_3387_ = lean_apply_1(v_fst_3342_, lean_box(0));
v___x_3388_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3386_, v___x_3355_, v___x_3387_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
v___y_3361_ = v___x_3388_;
goto v___jp_3360_;
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3411_; 
v_a_3389_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3391_ = v___x_3383_;
v_isShared_3392_ = v_isSharedCheck_3411_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3383_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3411_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
uint8_t v___x_3393_; 
v___x_3393_ = l_Lean_Exception_isInterrupt(v_a_3389_);
if (v___x_3393_ == 0)
{
uint8_t v___x_3394_; 
lean_inc(v_a_3389_);
v___x_3394_ = l_Lean_Exception_isRuntime(v_a_3389_);
if (v___x_3394_ == 0)
{
lean_object* v___x_3395_; 
lean_del_object(v___x_3391_);
lean_dec(v_a_3389_);
v___x_3395_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3382_, v___x_3394_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3395_) == 0)
{
lean_dec_ref_known(v___x_3395_, 1);
v_a_3343_ = v_snd_3359_;
v_b_3344_ = v___x_3356_;
goto _start;
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_snd_3359_);
lean_dec_ref(v_fst_3342_);
v_a_3397_ = lean_ctor_get(v___x_3395_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3395_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3395_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v___x_3406_; 
lean_dec(v_a_3382_);
lean_dec(v_snd_3359_);
lean_dec_ref(v_fst_3342_);
if (v_isShared_3392_ == 0)
{
v___x_3406_ = v___x_3391_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3389_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
else
{
lean_object* v___x_3409_; 
lean_dec(v_a_3382_);
lean_dec(v_snd_3359_);
lean_dec_ref(v_fst_3342_);
if (v_isShared_3392_ == 0)
{
v___x_3409_ = v___x_3391_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3389_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v_snd_3359_);
lean_dec(v_fst_3358_);
lean_dec_ref(v_fst_3342_);
v_a_3412_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3381_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3381_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
v___jp_3360_:
{
if (lean_obj_tag(v___y_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3372_; 
v_a_3362_ = lean_ctor_get(v___y_3361_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___y_3361_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3364_ = v___y_3361_;
v_isShared_3365_ = v_isSharedCheck_3372_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___y_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3372_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
if (lean_obj_tag(v_a_3362_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3368_; 
lean_dec(v_snd_3359_);
lean_dec_ref(v_fst_3342_);
v_a_3366_ = lean_ctor_get(v_a_3362_, 0);
lean_inc(v_a_3366_);
lean_dec_ref_known(v_a_3362_, 1);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v_a_3366_);
v___x_3368_ = v___x_3364_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3366_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
else
{
lean_object* v_a_3370_; 
lean_del_object(v___x_3364_);
v_a_3370_ = lean_ctor_get(v_a_3362_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v_a_3362_, 1);
v_a_3343_ = v_snd_3359_;
v_b_3344_ = v_a_3370_;
goto _start;
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v_snd_3359_);
lean_dec_ref(v_fst_3342_);
v_a_3373_ = lean_ctor_get(v___y_3361_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___y_3361_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___y_3361_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___y_3361_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_3420_, lean_object* v_fst_3421_, lean_object* v_a_3422_, lean_object* v_b_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
uint8_t v_cancel_boxed_3433_; lean_object* v_res_3434_; 
v_cancel_boxed_3433_ = lean_unbox(v_cancel_3420_);
v_res_3434_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_boxed_3433_, v_fst_3421_, v_a_3422_, v_b_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(lean_object* v_msg_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_ref_3441_; lean_object* v___x_3442_; lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3451_; 
v_ref_3441_ = lean_ctor_get(v___y_3438_, 2);
v___x_3442_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_inc(v_ref_3441_);
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v_ref_3441_);
lean_ctor_set(v___x_3447_, 1, v_a_3443_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set_tag(v___x_3445_, 1);
lean_ctor_set(v___x_3445_, 0, v___x_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg(lean_object* v_jobs_3459_, uint8_t v_cancel_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_3459_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
if (lean_obj_tag(v___x_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v_fst_3472_; lean_object* v_snd_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
lean_inc(v_a_3471_);
lean_dec_ref_known(v___x_3470_, 1);
v_fst_3472_ = lean_ctor_get(v_a_3471_, 0);
lean_inc(v_fst_3472_);
v_snd_3473_ = lean_ctor_get(v_a_3471_, 1);
lean_inc(v_snd_3473_);
lean_dec(v_a_3471_);
v___x_3474_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_3475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3460_, v_fst_3472_, v_snd_3473_, v___x_3474_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3487_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3487_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3487_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v_fst_3480_; 
v_fst_3480_ = lean_ctor_get(v_a_3476_, 0);
lean_inc(v_fst_3480_);
lean_dec(v_a_3476_);
if (lean_obj_tag(v_fst_3480_) == 0)
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
lean_del_object(v___x_3478_);
v___x_3481_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_3482_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v___x_3481_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
return v___x_3482_;
}
else
{
lean_object* v_val_3483_; lean_object* v___x_3485_; 
v_val_3483_ = lean_ctor_get(v_fst_3480_, 0);
lean_inc(v_val_3483_);
lean_dec_ref_known(v_fst_3480_, 1);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v_val_3483_);
v___x_3485_ = v___x_3478_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_val_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
v_a_3488_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3475_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3475_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
v_a_3496_ = lean_ctor_get(v___x_3470_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3470_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3470_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3470_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg___boxed(lean_object* v_jobs_3504_, lean_object* v_cancel_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_){
_start:
{
uint8_t v_cancel_boxed_3515_; lean_object* v_res_3516_; 
v_cancel_boxed_3515_ = lean_unbox(v_cancel_3505_);
v_res_3516_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3504_, v_cancel_boxed_3515_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec_ref(v_a_3510_);
lean_dec(v_a_3509_);
lean_dec_ref(v_a_3508_);
lean_dec(v_a_3507_);
lean_dec_ref(v_a_3506_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst(lean_object* v_00_u03b1_3517_, lean_object* v_jobs_3518_, uint8_t v_cancel_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3518_, v_cancel_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___boxed(lean_object* v_00_u03b1_3530_, lean_object* v_jobs_3531_, lean_object* v_cancel_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
uint8_t v_cancel_boxed_3542_; lean_object* v_res_3543_; 
v_cancel_boxed_3542_ = lean_unbox(v_cancel_3532_);
v_res_3543_ = l_Lean_Elab_Tactic_TacticM_parFirst(v_00_u03b1_3530_, v_jobs_3531_, v_cancel_boxed_3542_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(lean_object* v_00_u03b1_3544_, uint8_t v_cancel_3545_, lean_object* v_fst_3546_, lean_object* v_inst_3547_, lean_object* v_R_3548_, lean_object* v_a_3549_, lean_object* v_b_3550_, lean_object* v_c_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3545_, v_fst_3546_, v_a_3549_, v_b_3550_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_3562_ = _args[0];
lean_object* v_cancel_3563_ = _args[1];
lean_object* v_fst_3564_ = _args[2];
lean_object* v_inst_3565_ = _args[3];
lean_object* v_R_3566_ = _args[4];
lean_object* v_a_3567_ = _args[5];
lean_object* v_b_3568_ = _args[6];
lean_object* v_c_3569_ = _args[7];
lean_object* v___y_3570_ = _args[8];
lean_object* v___y_3571_ = _args[9];
lean_object* v___y_3572_ = _args[10];
lean_object* v___y_3573_ = _args[11];
lean_object* v___y_3574_ = _args[12];
lean_object* v___y_3575_ = _args[13];
lean_object* v___y_3576_ = _args[14];
lean_object* v___y_3577_ = _args[15];
lean_object* v___y_3578_ = _args[16];
_start:
{
uint8_t v_cancel_boxed_3579_; lean_object* v_res_3580_; 
v_cancel_boxed_3579_ = lean_unbox(v_cancel_3563_);
v_res_3580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(v_00_u03b1_3562_, v_cancel_boxed_3579_, v_fst_3564_, v_inst_3565_, v_R_3566_, v_a_3567_, v_b_3568_, v_c_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(lean_object* v_00_u03b1_3581_, lean_object* v_msg_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3582_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_3593_, lean_object* v_msg_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(v_00_u03b1_3593_, v_msg_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
return v_res_3604_;
}
}
lean_object* runtime_initialize_Lean_Elab_Task(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Parallel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Parallel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Task(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Parallel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Task(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Parallel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Parallel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Parallel(builtin);
}
#ifdef __cplusplus
}
#endif
