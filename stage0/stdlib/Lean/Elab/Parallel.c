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
lean_object* l_Lean_Elab_Tactic_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v_head_273_; lean_object* v_tail_274_; lean_object* v_a_276_; lean_object* v___y_280_; uint8_t v___y_281_; lean_object* v_a_285_; lean_object* v___x_1808__overap_288_; lean_object* v___x_289_; 
v_head_273_ = lean_ctor_get(v_as_x27_267_, 0);
v_tail_274_ = lean_ctor_get(v_as_x27_267_, 1);
lean_inc(v_head_273_);
v___x_1808__overap_288_ = lean_task_get_own(v_head_273_);
lean_inc(v___y_270_);
lean_inc_ref(v___y_269_);
v___x_289_ = lean_apply_3(v___x_1808__overap_288_, v___y_269_, v___y_270_, lean_box(0));
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_291_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
lean_dec_ref_known(v___x_289_, 1);
v___x_291_ = l_Lean_Core_saveState___redArg(v___y_270_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_300_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_a_290_);
lean_ctor_set(v___x_296_, 1, v_a_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 1);
lean_ctor_set(v___x_294_, 0, v___x_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
v_a_276_ = v___x_298_;
goto v___jp_275_;
}
}
}
else
{
lean_object* v_a_301_; 
lean_dec(v_a_290_);
v_a_301_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_301_);
lean_dec_ref_known(v___x_291_, 1);
v_a_285_ = v_a_301_;
goto v___jp_284_;
}
}
else
{
lean_object* v_a_302_; 
v_a_302_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v___x_289_, 1);
v_a_285_ = v_a_302_;
goto v___jp_284_;
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
if (v___y_281_ == 0)
{
lean_object* v___x_282_; 
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___y_280_);
v_a_276_ = v___x_282_;
goto v___jp_275_;
}
else
{
lean_object* v___x_283_; 
lean_dec(v_b_268_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v___y_280_);
return v___x_283_;
}
}
v___jp_284_:
{
uint8_t v___x_286_; 
v___x_286_ = l_Lean_Exception_isInterrupt(v_a_285_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; 
lean_inc_ref(v_a_285_);
v___x_287_ = l_Lean_Exception_isRuntime(v_a_285_);
v___y_280_ = v_a_285_;
v___y_281_ = v___x_287_;
goto v___jp_279_;
}
else
{
v___y_280_ = v_a_285_;
v___y_281_ = v___x_286_;
goto v___jp_279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg___boxed(lean_object* v_as_x27_303_, lean_object* v_b_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_303_, v_b_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v_as_x27_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = l_List_reverse___redArg(v_x_310_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
else
{
lean_object* v_head_316_; lean_object* v_tail_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_335_; 
v_head_316_ = lean_ctor_get(v_x_309_, 0);
v_tail_317_ = lean_ctor_get(v_x_309_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_309_);
if (v_isSharedCheck_335_ == 0)
{
v___x_319_ = v_x_309_;
v_isShared_320_ = v_isSharedCheck_335_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_tail_317_);
lean_inc(v_head_316_);
lean_dec(v_x_309_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_335_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_head_316_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v_x_310_);
lean_ctor_set(v___x_319_, 0, v_a_322_);
v___x_324_ = v___x_319_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_322_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_x_310_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v_x_309_ = v_tail_317_;
v_x_310_ = v___x_324_;
goto _start;
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_del_object(v___x_319_);
lean_dec(v_tail_317_);
lean_dec(v_x_310_);
v_a_327_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_321_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_321_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg___boxed(lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_336_, v_x_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg(lean_object* v_jobs_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_st_ref_get(v_a_344_);
v___x_347_ = lean_box(0);
v___x_348_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_342_, v___x_347_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_a_349_, v___x_347_, v_a_343_, v_a_344_);
lean_dec(v_a_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_360_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_360_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_355_ = lean_st_ref_swap(v_a_344_, v___x_346_);
lean_dec(v___x_355_);
v___x_356_ = l_List_reverse___redArg(v_a_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_356_);
v___x_358_ = v___x_353_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
else
{
lean_dec(v___x_346_);
return v___x_350_;
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v___x_346_);
v_a_361_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_348_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_348_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg___boxed(lean_object* v_jobs_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Core_CoreM_par___redArg(v_jobs_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par(lean_object* v_00_u03b1_374_, lean_object* v_jobs_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Core_CoreM_par___redArg(v_jobs_375_, v_a_376_, v_a_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___boxed(lean_object* v_00_u03b1_380_, lean_object* v_jobs_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Core_CoreM_par(v_00_u03b1_380_, v_jobs_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(lean_object* v_00_u03b1_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_387_, v_x_388_, v___y_389_, v___y_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___boxed(lean_object* v_00_u03b1_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(v_00_u03b1_393_, v_x_394_, v_x_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(lean_object* v_00_u03b1_400_, lean_object* v_as_401_, lean_object* v_as_x27_402_, lean_object* v_b_403_, lean_object* v_a_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_402_, v_b_403_, v___y_405_, v___y_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___boxed(lean_object* v_00_u03b1_409_, lean_object* v_as_410_, lean_object* v_as_x27_411_, lean_object* v_b_412_, lean_object* v_a_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(v_00_u03b1_409_, v_as_410_, v_as_x27_411_, v_b_412_, v_a_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v_as_x27_411_);
lean_dec(v_as_410_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(lean_object* v_as_x27_418_, lean_object* v_b_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
if (lean_obj_tag(v_as_x27_418_) == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_b_419_);
return v___x_423_;
}
else
{
lean_object* v_head_424_; lean_object* v_tail_425_; lean_object* v___x_1618__overap_426_; lean_object* v___x_427_; 
v_head_424_ = lean_ctor_get(v_as_x27_418_, 0);
v_tail_425_ = lean_ctor_get(v_as_x27_418_, 1);
lean_inc(v_head_424_);
v___x_1618__overap_426_ = lean_task_get_own(v_head_424_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
v___x_427_ = lean_apply_3(v___x_1618__overap_426_, v___y_420_, v___y_421_, lean_box(0));
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v_a_428_);
v___x_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v_b_419_);
v_as_x27_418_ = v_tail_425_;
v_b_419_ = v___x_430_;
goto _start;
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_446_; 
v_a_432_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_446_ == 0)
{
v___x_434_ = v___x_427_;
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_427_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_446_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v___y_437_; uint8_t v___x_444_; 
v___x_444_ = l_Lean_Exception_isInterrupt(v_a_432_);
if (v___x_444_ == 0)
{
uint8_t v___x_445_; 
lean_inc(v_a_432_);
v___x_445_ = l_Lean_Exception_isRuntime(v_a_432_);
v___y_437_ = v___x_445_;
goto v___jp_436_;
}
else
{
v___y_437_ = v___x_444_;
goto v___jp_436_;
}
v___jp_436_:
{
if (v___y_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; 
lean_del_object(v___x_434_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v_a_432_);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_b_419_);
v_as_x27_418_ = v_tail_425_;
v_b_419_ = v___x_439_;
goto _start;
}
else
{
lean_object* v___x_442_; 
lean_dec(v_b_419_);
if (v_isShared_435_ == 0)
{
v___x_442_ = v___x_434_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_432_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_447_, v_b_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v_as_x27_447_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg(lean_object* v_jobs_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_st_ref_get(v_a_455_);
v___x_458_ = lean_box(0);
v___x_459_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_453_, v___x_458_, v_a_454_, v_a_455_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_461_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_459_, 1);
v___x_461_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_a_460_, v___x_458_, v_a_454_, v_a_455_);
lean_dec(v_a_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_471_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_471_ == 0)
{
v___x_464_ = v___x_461_;
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_461_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_471_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = lean_st_ref_swap(v_a_455_, v___x_457_);
lean_dec(v___x_466_);
v___x_467_ = l_List_reverse___redArg(v_a_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_467_);
v___x_469_ = v___x_464_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
else
{
lean_dec(v___x_457_);
return v___x_461_;
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec(v___x_457_);
v_a_472_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_459_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_459_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg___boxed(lean_object* v_jobs_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_480_, v_a_481_, v_a_482_);
lean_dec(v_a_482_);
lean_dec_ref(v_a_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27(lean_object* v_00_u03b1_485_, lean_object* v_jobs_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_486_, v_a_487_, v_a_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___boxed(lean_object* v_00_u03b1_491_, lean_object* v_jobs_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Core_CoreM_par_x27(v_00_u03b1_491_, v_jobs_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(lean_object* v_00_u03b1_497_, lean_object* v_as_498_, lean_object* v_as_x27_499_, lean_object* v_b_500_, lean_object* v_a_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_499_, v_b_500_, v___y_502_, v___y_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_506_, lean_object* v_as_507_, lean_object* v_as_x27_508_, lean_object* v_b_509_, lean_object* v_a_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(v_00_u03b1_506_, v_as_507_, v_as_x27_508_, v_b_509_, v_a_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v_as_x27_508_);
lean_dec(v_as_507_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_515_, lean_object* v___x_516_, lean_object* v_____r_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_a_515_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_516_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_525_, lean_object* v___x_526_, lean_object* v_____r_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_525_, v___x_526_, v_____r_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(uint8_t v_cancel_535_, lean_object* v_fst_536_, lean_object* v_a_537_, lean_object* v_b_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
if (lean_obj_tag(v_a_537_) == 0)
{
lean_object* v___x_542_; 
lean_dec_ref(v_fst_536_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v_b_538_);
return v___x_542_;
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___y_549_; lean_object* v___x_569_; 
lean_dec_ref(v_b_538_);
v___x_543_ = lean_box(0);
v___x_544_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_545_ = l_IO_waitAny_x27___redArg(v_a_537_);
v_fst_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_fst_546_);
v_snd_547_ = lean_ctor_get(v___x_545_, 1);
lean_inc(v_snd_547_);
lean_dec_ref(v___x_545_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
v___x_569_ = lean_apply_3(v_fst_546_, v___y_539_, v___y_540_, lean_box(0));
if (lean_obj_tag(v___x_569_) == 0)
{
if (v_cancel_535_ == 0)
{
lean_object* v_a_570_; lean_object* v___x_571_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_570_, v___x_543_, v___x_543_, v___y_539_, v___y_540_);
v___y_549_ = v___x_571_;
goto v___jp_548_;
}
else
{
lean_object* v_a_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_a_572_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_569_, 1);
lean_inc_ref(v_fst_536_);
v___x_573_ = lean_apply_1(v_fst_536_, lean_box(0));
v___x_574_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_572_, v___x_543_, v___x_573_, v___y_539_, v___y_540_);
v___y_549_ = v___x_574_;
goto v___jp_548_;
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_587_; 
v_a_575_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_587_ == 0)
{
v___x_577_ = v___x_569_;
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_569_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_587_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
uint8_t v___y_580_; uint8_t v___x_585_; 
v___x_585_ = l_Lean_Exception_isInterrupt(v_a_575_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
lean_inc(v_a_575_);
v___x_586_ = l_Lean_Exception_isRuntime(v_a_575_);
v___y_580_ = v___x_586_;
goto v___jp_579_;
}
else
{
v___y_580_ = v___x_585_;
goto v___jp_579_;
}
v___jp_579_:
{
if (v___y_580_ == 0)
{
lean_del_object(v___x_577_);
lean_dec(v_a_575_);
v_a_537_ = v_snd_547_;
v_b_538_ = v___x_544_;
goto _start;
}
else
{
lean_object* v___x_583_; 
lean_dec(v_snd_547_);
lean_dec_ref(v_fst_536_);
if (v_isShared_578_ == 0)
{
v___x_583_ = v___x_577_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_575_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
}
v___jp_548_:
{
if (lean_obj_tag(v___y_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_560_; 
v_a_550_ = lean_ctor_get(v___y_549_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___y_549_);
if (v_isSharedCheck_560_ == 0)
{
v___x_552_ = v___y_549_;
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___y_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_560_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
if (lean_obj_tag(v_a_550_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; 
lean_dec(v_snd_547_);
lean_dec_ref(v_fst_536_);
v_a_554_ = lean_ctor_get(v_a_550_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v_a_550_, 1);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v_a_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v_a_558_; 
lean_del_object(v___x_552_);
v_a_558_ = lean_ctor_get(v_a_550_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v_a_550_, 1);
v_a_537_ = v_snd_547_;
v_b_538_ = v_a_558_;
goto _start;
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_snd_547_);
lean_dec_ref(v_fst_536_);
v_a_561_ = lean_ctor_get(v___y_549_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___y_549_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___y_549_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___y_549_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
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
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_601_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
lean_ctor_set(v___x_603_, 2, v___x_602_);
lean_ctor_set(v___x_603_, 3, v___x_602_);
lean_ctor_set(v___x_603_, 4, v___x_601_);
lean_ctor_set(v___x_603_, 5, v___x_601_);
lean_ctor_set(v___x_603_, 6, v___x_601_);
lean_ctor_set(v___x_603_, 7, v___x_601_);
lean_ctor_set(v___x_603_, 8, v___x_601_);
lean_ctor_set(v___x_603_, 9, v___x_601_);
lean_ctor_set(v___x_603_, 10, v___x_601_);
lean_ctor_set(v___x_603_, 11, v___x_600_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(32u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_607_ = ((size_t)5ULL);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_unsigned_to_nat(32u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
v___x_611_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3);
v___x_612_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_610_);
lean_ctor_set(v___x_612_, 2, v___x_608_);
lean_ctor_set(v___x_612_, 3, v___x_608_);
lean_ctor_set_usize(v___x_612_, 4, v___x_607_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_613_ = lean_box(1);
v___x_614_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4);
v___x_615_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
lean_ctor_set(v___x_616_, 2, v___x_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(lean_object* v_msgData_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v___x_621_; lean_object* v_toCold_622_; lean_object* v_env_623_; lean_object* v_options_624_; uint8_t v___x_625_; lean_object* v_env_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_621_ = lean_st_ref_get(v___y_619_);
v_toCold_622_ = lean_ctor_get(v___y_618_, 0);
v_env_623_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_621_);
v_options_624_ = lean_ctor_get(v_toCold_622_, 2);
v___x_625_ = 0;
v_env_626_ = l_Lean_Environment_setRecordingDeps(v_env_623_, v___x_625_);
v___x_627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2);
v___x_628_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_624_);
v___x_629_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_629_, 0, v_env_626_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_ctor_set(v___x_629_, 3, v_options_624_);
v___x_630_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v_msgData_617_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msgData_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_ref_641_; lean_object* v___x_642_; lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_651_; 
v_ref_641_ = lean_ctor_get(v___y_638_, 2);
v___x_642_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msg_637_, v___y_638_, v___y_639_);
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_651_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_651_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
lean_inc(v_ref_641_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v_ref_641_);
lean_ctor_set(v___x_647_, 1, v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 1);
lean_ctor_set(v___x_645_, 0, v___x_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
return v_res_656_;
}
}
static lean_object* _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lean_Core_CoreM_parFirst___redArg___closed__0));
v___x_659_ = l_Lean_stringToMessageData(v___x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg(lean_object* v_jobs_660_, uint8_t v_cancel_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_660_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v_fst_667_; lean_object* v_snd_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v_fst_667_ = lean_ctor_get(v_a_666_, 0);
lean_inc(v_fst_667_);
v_snd_668_ = lean_ctor_get(v_a_666_, 1);
lean_inc(v_snd_668_);
lean_dec(v_a_666_);
v___x_669_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_661_, v_fst_667_, v_snd_668_, v___x_669_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_682_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_682_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_fst_675_; 
v_fst_675_ = lean_ctor_get(v_a_671_, 0);
lean_inc(v_fst_675_);
lean_dec(v_a_671_);
if (lean_obj_tag(v_fst_675_) == 0)
{
lean_object* v___x_676_; lean_object* v___x_677_; 
lean_del_object(v___x_673_);
v___x_676_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_677_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v___x_676_, v_a_662_, v_a_663_);
return v___x_677_;
}
else
{
lean_object* v_val_678_; lean_object* v___x_680_; 
v_val_678_ = lean_ctor_get(v_fst_675_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v_fst_675_, 1);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_val_678_);
v___x_680_ = v___x_673_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_val_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
v_a_683_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_670_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_670_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_a_691_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_665_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_665_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg___boxed(lean_object* v_jobs_699_, lean_object* v_cancel_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
uint8_t v_cancel_boxed_704_; lean_object* v_res_705_; 
v_cancel_boxed_704_ = lean_unbox(v_cancel_700_);
v_res_705_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_699_, v_cancel_boxed_704_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst(lean_object* v_00_u03b1_706_, lean_object* v_jobs_707_, uint8_t v_cancel_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_707_, v_cancel_708_, v_a_709_, v_a_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___boxed(lean_object* v_00_u03b1_713_, lean_object* v_jobs_714_, lean_object* v_cancel_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
uint8_t v_cancel_boxed_719_; lean_object* v_res_720_; 
v_cancel_boxed_719_ = lean_unbox(v_cancel_715_);
v_res_720_ = l_Lean_Core_CoreM_parFirst(v_00_u03b1_713_, v_jobs_714_, v_cancel_boxed_719_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(lean_object* v_00_u03b1_721_, uint8_t v_cancel_722_, lean_object* v_fst_723_, lean_object* v_inst_724_, lean_object* v_R_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v_c_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_722_, v_fst_723_, v_a_726_, v_b_727_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_733_, lean_object* v_cancel_734_, lean_object* v_fst_735_, lean_object* v_inst_736_, lean_object* v_R_737_, lean_object* v_a_738_, lean_object* v_b_739_, lean_object* v_c_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
uint8_t v_cancel_boxed_744_; lean_object* v_res_745_; 
v_cancel_boxed_744_ = lean_unbox(v_cancel_734_);
v_res_745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(v_00_u03b1_733_, v_cancel_boxed_744_, v_fst_735_, v_inst_736_, v_R_737_, v_a_738_, v_b_739_, v_c_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(lean_object* v_00_u03b1_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_747_, v___y_748_, v___y_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_752_, lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(v_00_u03b1_752_, v_msg_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = l_List_reverse___redArg(v_x_759_);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
else
{
lean_object* v_head_767_; lean_object* v_tail_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_786_; 
v_head_767_ = lean_ctor_get(v_x_758_, 0);
v_tail_768_ = lean_ctor_get(v_x_758_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_786_ == 0)
{
v___x_770_ = v_x_758_;
v_isShared_771_ = v_isSharedCheck_786_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_tail_768_);
lean_inc(v_head_767_);
lean_dec(v_x_758_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_786_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_head_767_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_a_773_; lean_object* v___x_775_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_a_773_);
lean_dec_ref_known(v___x_772_, 1);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_x_759_);
lean_ctor_set(v___x_770_, 0, v_a_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_773_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_x_759_);
v___x_775_ = v_reuseFailAlloc_777_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
v_x_758_ = v_tail_768_;
v_x_759_ = v___x_775_;
goto _start;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_del_object(v___x_770_);
lean_dec(v_tail_768_);
lean_dec(v_x_759_);
v_a_778_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_772_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_772_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_787_, v_x_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(lean_object* v_as_x27_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
if (lean_obj_tag(v_as_x27_795_) == 0)
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v_b_796_);
return v___x_802_;
}
else
{
lean_object* v_head_803_; lean_object* v_tail_804_; lean_object* v_a_806_; lean_object* v___y_810_; uint8_t v___y_811_; lean_object* v_a_815_; lean_object* v___x_2356__overap_818_; lean_object* v___x_819_; 
v_head_803_ = lean_ctor_get(v_as_x27_795_, 0);
v_tail_804_ = lean_ctor_get(v_as_x27_795_, 1);
lean_inc(v_head_803_);
v___x_2356__overap_818_ = lean_task_get_own(v_head_803_);
lean_inc(v___y_800_);
lean_inc_ref(v___y_799_);
lean_inc(v___y_798_);
lean_inc_ref(v___y_797_);
v___x_819_ = lean_apply_5(v___x_2356__overap_818_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, lean_box(0));
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_821_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v___x_821_ = l_Lean_Meta_saveState___redArg(v___y_798_, v___y_800_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_830_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_a_820_);
lean_ctor_set(v___x_826_, 1, v_a_822_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 1);
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v_a_806_ = v___x_828_;
goto v___jp_805_;
}
}
}
else
{
lean_object* v_a_831_; 
lean_dec(v_a_820_);
v_a_831_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_821_, 1);
v_a_815_ = v_a_831_;
goto v___jp_814_;
}
}
else
{
lean_object* v_a_832_; 
v_a_832_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_819_, 1);
v_a_815_ = v_a_832_;
goto v___jp_814_;
}
v___jp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_806_);
lean_ctor_set(v___x_807_, 1, v_b_796_);
v_as_x27_795_ = v_tail_804_;
v_b_796_ = v___x_807_;
goto _start;
}
v___jp_809_:
{
if (v___y_811_ == 0)
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___y_810_);
v_a_806_ = v___x_812_;
goto v___jp_805_;
}
else
{
lean_object* v___x_813_; 
lean_dec(v_b_796_);
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v___y_810_);
return v___x_813_;
}
}
v___jp_814_:
{
uint8_t v___x_816_; 
v___x_816_ = l_Lean_Exception_isInterrupt(v_a_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; 
lean_inc_ref(v_a_815_);
v___x_817_ = l_Lean_Exception_isRuntime(v_a_815_);
v___y_810_ = v_a_815_;
v___y_811_ = v___x_817_;
goto v___jp_809_;
}
else
{
v___y_810_ = v_a_815_;
v___y_811_ = v___x_816_;
goto v___jp_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg___boxed(lean_object* v_as_x27_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_833_, v_b_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v_as_x27_833_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg(lean_object* v_jobs_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = lean_st_ref_get(v_a_843_);
v___x_848_ = lean_box(0);
v___x_849_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_841_, v___x_848_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
v___x_851_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_a_850_, v___x_848_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_850_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_861_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_861_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_861_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_st_ref_swap(v_a_843_, v___x_847_);
lean_dec(v___x_856_);
v___x_857_ = l_List_reverse___redArg(v_a_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_dec(v___x_847_);
return v___x_851_;
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v___x_847_);
v_a_862_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_849_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_849_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg___boxed(lean_object* v_jobs_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par(lean_object* v_00_u03b1_877_, lean_object* v_jobs_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___boxed(lean_object* v_00_u03b1_885_, lean_object* v_jobs_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Meta_MetaM_par(v_00_u03b1_885_, v_jobs_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(lean_object* v_00_u03b1_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_894_, v_x_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___boxed(lean_object* v_00_u03b1_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(v_00_u03b1_902_, v_x_903_, v_x_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(lean_object* v_00_u03b1_911_, lean_object* v_as_912_, lean_object* v_as_x27_913_, lean_object* v_b_914_, lean_object* v_a_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_913_, v_b_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___boxed(lean_object* v_00_u03b1_922_, lean_object* v_as_923_, lean_object* v_as_x27_924_, lean_object* v_b_925_, lean_object* v_a_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(v_00_u03b1_922_, v_as_923_, v_as_x27_924_, v_b_925_, v_a_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v_as_x27_924_);
lean_dec(v_as_923_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(lean_object* v_as_x27_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
if (lean_obj_tag(v_as_x27_933_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v_b_934_);
return v___x_940_;
}
else
{
lean_object* v_head_941_; lean_object* v_tail_942_; lean_object* v___x_2059__overap_943_; lean_object* v___x_944_; 
v_head_941_ = lean_ctor_get(v_as_x27_933_, 0);
v_tail_942_ = lean_ctor_get(v_as_x27_933_, 1);
lean_inc(v_head_941_);
v___x_2059__overap_943_ = lean_task_get_own(v_head_941_);
lean_inc(v___y_938_);
lean_inc_ref(v___y_937_);
lean_inc(v___y_936_);
lean_inc_ref(v___y_935_);
v___x_944_ = lean_apply_5(v___x_2059__overap_943_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, lean_box(0));
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v_a_945_);
v___x_947_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v_b_934_);
v_as_x27_933_ = v_tail_942_;
v_b_934_ = v___x_947_;
goto _start;
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_963_; 
v_a_949_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_963_ == 0)
{
v___x_951_ = v___x_944_;
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_944_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_963_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v___y_954_; uint8_t v___x_961_; 
v___x_961_ = l_Lean_Exception_isInterrupt(v_a_949_);
if (v___x_961_ == 0)
{
uint8_t v___x_962_; 
lean_inc(v_a_949_);
v___x_962_ = l_Lean_Exception_isRuntime(v_a_949_);
v___y_954_ = v___x_962_;
goto v___jp_953_;
}
else
{
v___y_954_ = v___x_961_;
goto v___jp_953_;
}
v___jp_953_:
{
if (v___y_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_del_object(v___x_951_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_a_949_);
v___x_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v_b_934_);
v_as_x27_933_ = v_tail_942_;
v_b_934_ = v___x_956_;
goto _start;
}
else
{
lean_object* v___x_959_; 
lean_dec(v_b_934_);
if (v_isShared_952_ == 0)
{
v___x_959_ = v___x_951_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_949_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_964_, lean_object* v_b_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_964_, v_b_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v_as_x27_964_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg(lean_object* v_jobs_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_st_ref_get(v_a_974_);
v___x_979_ = lean_box(0);
v___x_980_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_972_, v___x_979_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_a_981_, v___x_979_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_981_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_992_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_992_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_992_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_987_ = lean_st_ref_swap(v_a_974_, v___x_978_);
lean_dec(v___x_987_);
v___x_988_ = l_List_reverse___redArg(v_a_983_);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_990_ = v___x_985_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
else
{
lean_dec(v___x_978_);
return v___x_982_;
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v___x_978_);
v_a_993_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_980_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_980_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg___boxed(lean_object* v_jobs_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27(lean_object* v_00_u03b1_1008_, lean_object* v_jobs_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_jobs_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Meta_MetaM_par_x27(v_00_u03b1_1016_, v_jobs_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(lean_object* v_00_u03b1_1024_, lean_object* v_as_1025_, lean_object* v_as_x27_1026_, lean_object* v_b_1027_, lean_object* v_a_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_1026_, v_b_1027_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_as_1036_, lean_object* v_as_x27_1037_, lean_object* v_b_1038_, lean_object* v_a_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(v_00_u03b1_1035_, v_as_1036_, v_as_x27_1037_, v_b_1038_, v_a_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v_as_x27_1037_);
lean_dec(v_as_1036_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
if (lean_obj_tag(v_x_1046_) == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = l_List_reverse___redArg(v_x_1047_);
v___x_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
return v___x_1054_;
}
else
{
lean_object* v_head_1055_; lean_object* v_tail_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1074_; 
v_head_1055_ = lean_ctor_get(v_x_1046_, 0);
v_tail_1056_ = lean_ctor_get(v_x_1046_, 1);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1046_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1058_ = v_x_1046_;
v_isShared_1059_ = v_isSharedCheck_1074_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_tail_1056_);
lean_inc(v_head_1055_);
lean_dec(v_x_1046_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1074_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Meta_MetaM_asTask___redArg(v_head_1055_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 1, v_x_1047_);
lean_ctor_set(v___x_1058_, 0, v_a_1061_);
v___x_1063_ = v___x_1058_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1061_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_x_1047_);
v___x_1063_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
v_x_1046_ = v_tail_1056_;
v_x_1047_ = v___x_1063_;
goto _start;
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_del_object(v___x_1058_);
lean_dec(v_tail_1056_);
lean_dec(v_x_1047_);
v_a_1066_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1060_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1060_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1075_, v_x_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg(lean_object* v_jobs_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1083_, v___x_1089_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1109_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1109_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1109_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1108_; 
v___x_1095_ = l_List_unzipTR___redArg(v_a_1091_);
v_fst_1096_ = lean_ctor_get(v___x_1095_, 0);
v_snd_1097_ = lean_ctor_get(v___x_1095_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1099_ = v___x_1095_;
v_isShared_1100_ = v_isSharedCheck_1108_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_snd_1097_);
lean_inc(v_fst_1096_);
lean_dec(v___x_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1108_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1101_, 0, v_fst_1096_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1101_);
v___x_1103_ = v___x_1099_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_snd_1097_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1105_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1103_);
v___x_1105_ = v___x_1093_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1090_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1090_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel(lean_object* v_00_u03b1_1125_, lean_object* v_jobs_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1133_, lean_object* v_jobs_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Meta_MetaM_parIterWithCancel(v_00_u03b1_1133_, v_jobs_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1142_, v_x_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(v_00_u03b1_1150_, v_x_1151_, v_x_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg(lean_object* v_jobs_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1174_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1174_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_snd_1170_; lean_object* v___x_1172_; 
v_snd_1170_ = lean_ctor_get(v_a_1166_, 1);
lean_inc(v_snd_1170_);
lean_dec(v_a_1166_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v_snd_1170_);
v___x_1172_ = v___x_1168_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_snd_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1165_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1165_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg___boxed(lean_object* v_jobs_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter(lean_object* v_00_u03b1_1190_, lean_object* v_jobs_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_jobs_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_MetaM_parIter(v_00_u03b1_1198_, v_jobs_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1206_, v___x_1212_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1232_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1232_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v_fst_1219_; lean_object* v_snd_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1231_; 
v___x_1218_ = l_List_unzipTR___redArg(v_a_1214_);
v_fst_1219_ = lean_ctor_get(v___x_1218_, 0);
v_snd_1220_ = lean_ctor_get(v___x_1218_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1222_ = v___x_1218_;
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_snd_1220_);
lean_inc(v_fst_1219_);
lean_dec(v___x_1218_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1231_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1224_, 0, v_fst_1219_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_snd_1220_);
v___x_1226_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
lean_object* v___x_1228_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1226_);
v___x_1228_ = v___x_1216_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
v_a_1233_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1213_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1213_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1248_, lean_object* v_jobs_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_jobs_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel(v_00_u03b1_1256_, v_jobs_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg(lean_object* v_jobs_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1273_ = v___x_1270_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1270_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_snd_1275_; lean_object* v___x_1277_; 
v_snd_1275_ = lean_ctor_get(v_a_1271_, 1);
lean_inc(v_snd_1275_);
lean_dec(v_a_1271_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_snd_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_snd_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1270_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1270_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy(lean_object* v_00_u03b1_1295_, lean_object* v_jobs_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___boxed(lean_object* v_00_u03b1_1303_, lean_object* v_jobs_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_MetaM_parIterGreedy(v_00_u03b1_1303_, v_jobs_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_1311_, lean_object* v___x_1312_, lean_object* v_____r_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_a_1311_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___x_1312_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_1323_, lean_object* v___x_1324_, lean_object* v_____r_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1323_, v___x_1324_, v_____r_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(uint8_t v_cancel_1332_, lean_object* v_fst_1333_, lean_object* v_a_1334_, lean_object* v_b_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
if (lean_obj_tag(v_a_1334_) == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v_fst_1333_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_b_1335_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___y_1348_; lean_object* v___x_1368_; 
lean_dec_ref(v_b_1335_);
v___x_1342_ = lean_box(0);
v___x_1343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1344_ = l_IO_waitAny_x27___redArg(v_a_1334_);
v_fst_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_fst_1345_);
v_snd_1346_ = lean_ctor_get(v___x_1344_, 1);
lean_inc(v_snd_1346_);
lean_dec_ref(v___x_1344_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
v___x_1368_ = lean_apply_5(v_fst_1345_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
if (lean_obj_tag(v___x_1368_) == 0)
{
if (v_cancel_1332_ == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
lean_dec_ref_known(v___x_1368_, 1);
v___x_1370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1369_, v___x_1342_, v___x_1342_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
v___y_1348_ = v___x_1370_;
goto v___jp_1347_;
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_a_1371_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1371_);
lean_dec_ref_known(v___x_1368_, 1);
lean_inc_ref(v_fst_1333_);
v___x_1372_ = lean_apply_1(v_fst_1333_, lean_box(0));
v___x_1373_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1371_, v___x_1342_, v___x_1372_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
v___y_1348_ = v___x_1373_;
goto v___jp_1347_;
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1386_; 
v_a_1374_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1376_ = v___x_1368_;
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1368_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
uint8_t v___y_1379_; uint8_t v___x_1384_; 
v___x_1384_ = l_Lean_Exception_isInterrupt(v_a_1374_);
if (v___x_1384_ == 0)
{
uint8_t v___x_1385_; 
lean_inc(v_a_1374_);
v___x_1385_ = l_Lean_Exception_isRuntime(v_a_1374_);
v___y_1379_ = v___x_1385_;
goto v___jp_1378_;
}
else
{
v___y_1379_ = v___x_1384_;
goto v___jp_1378_;
}
v___jp_1378_:
{
if (v___y_1379_ == 0)
{
lean_del_object(v___x_1376_);
lean_dec(v_a_1374_);
v_a_1334_ = v_snd_1346_;
v_b_1335_ = v___x_1343_;
goto _start;
}
else
{
lean_object* v___x_1382_; 
lean_dec(v_snd_1346_);
lean_dec_ref(v_fst_1333_);
if (v_isShared_1377_ == 0)
{
v___x_1382_ = v___x_1376_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1374_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
v___jp_1347_:
{
if (lean_obj_tag(v___y_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_a_1349_ = lean_ctor_get(v___y_1348_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___y_1348_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1351_ = v___y_1348_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___y_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
if (lean_obj_tag(v_a_1349_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; 
lean_dec(v_snd_1346_);
lean_dec_ref(v_fst_1333_);
v_a_1353_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v_a_1349_, 1);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v_a_1353_);
v___x_1355_ = v___x_1351_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v_a_1357_; 
lean_del_object(v___x_1351_);
v_a_1357_ = lean_ctor_get(v_a_1349_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v_a_1349_, 1);
v_a_1334_ = v_snd_1346_;
v_b_1335_ = v_a_1357_;
goto _start;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_snd_1346_);
lean_dec_ref(v_fst_1333_);
v_a_1360_ = lean_ctor_get(v___y_1348_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___y_1348_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___y_1348_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___y_1348_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_1387_, lean_object* v_fst_1388_, lean_object* v_a_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
uint8_t v_cancel_boxed_1396_; lean_object* v_res_1397_; 
v_cancel_boxed_1396_ = lean_unbox(v_cancel_1387_);
v_res_1397_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_boxed_1396_, v_fst_1388_, v_a_1389_, v_b_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(lean_object* v_msgData_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; uint8_t v___x_1406_; lean_object* v_env_1407_; lean_object* v___x_1408_; lean_object* v_toCold_1409_; lean_object* v_mctx_1410_; lean_object* v_lctx_1411_; lean_object* v_options_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1404_ = lean_st_ref_get(v___y_1402_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = 0;
v_env_1407_ = l_Lean_Environment_setRecordingDeps(v_env_1405_, v___x_1406_);
v___x_1408_ = lean_st_ref_get(v___y_1400_);
v_toCold_1409_ = lean_ctor_get(v___y_1401_, 0);
v_mctx_1410_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_ref(v_mctx_1410_);
lean_dec(v___x_1408_);
v_lctx_1411_ = lean_ctor_get(v___y_1399_, 2);
v_options_1412_ = lean_ctor_get(v_toCold_1409_, 2);
lean_inc_ref(v_options_1412_);
lean_inc_ref(v_lctx_1411_);
v___x_1413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1413_, 0, v_env_1407_);
lean_ctor_set(v___x_1413_, 1, v_mctx_1410_);
lean_ctor_set(v___x_1413_, 2, v_lctx_1411_);
lean_ctor_set(v___x_1413_, 3, v_options_1412_);
v___x_1414_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_msgData_1398_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msgData_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_ref_1429_; lean_object* v___x_1430_; lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1439_; 
v_ref_1429_ = lean_ctor_get(v___y_1426_, 2);
v___x_1430_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1433_ = v___x_1430_;
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1430_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1439_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1437_; 
lean_inc(v_ref_1429_);
v___x_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_ref_1429_);
lean_ctor_set(v___x_1435_, 1, v_a_1431_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set_tag(v___x_1433_, 1);
lean_ctor_set(v___x_1433_, 0, v___x_1435_);
v___x_1437_ = v___x_1433_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg(lean_object* v_jobs_1447_, uint8_t v_cancel_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1447_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v_fst_1456_; lean_object* v_snd_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v_fst_1456_ = lean_ctor_get(v_a_1455_, 0);
lean_inc(v_fst_1456_);
v_snd_1457_ = lean_ctor_get(v_a_1455_, 1);
lean_inc(v_snd_1457_);
lean_dec(v_a_1455_);
v___x_1458_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1459_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1448_, v_fst_1456_, v_snd_1457_, v___x_1458_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1471_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1471_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1471_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_fst_1464_; 
v_fst_1464_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_fst_1464_);
lean_dec(v_a_1460_);
if (lean_obj_tag(v_fst_1464_) == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_del_object(v___x_1462_);
v___x_1465_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_1466_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v___x_1465_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_);
return v___x_1466_;
}
else
{
lean_object* v_val_1467_; lean_object* v___x_1469_; 
v_val_1467_ = lean_ctor_get(v_fst_1464_, 0);
lean_inc(v_val_1467_);
lean_dec_ref_known(v_fst_1464_, 1);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v_val_1467_);
v___x_1469_ = v___x_1462_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_val_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
v_a_1472_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1459_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1459_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1454_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1454_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg___boxed(lean_object* v_jobs_1488_, lean_object* v_cancel_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
uint8_t v_cancel_boxed_1495_; lean_object* v_res_1496_; 
v_cancel_boxed_1495_ = lean_unbox(v_cancel_1489_);
v_res_1496_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1488_, v_cancel_boxed_1495_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
lean_dec(v_a_1493_);
lean_dec_ref(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec_ref(v_a_1490_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst(lean_object* v_00_u03b1_1497_, lean_object* v_jobs_1498_, uint8_t v_cancel_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1498_, v_cancel_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___boxed(lean_object* v_00_u03b1_1506_, lean_object* v_jobs_1507_, lean_object* v_cancel_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
uint8_t v_cancel_boxed_1514_; lean_object* v_res_1515_; 
v_cancel_boxed_1514_ = lean_unbox(v_cancel_1508_);
v_res_1515_ = l_Lean_Meta_MetaM_parFirst(v_00_u03b1_1506_, v_jobs_1507_, v_cancel_boxed_1514_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
lean_dec_ref(v_a_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(lean_object* v_00_u03b1_1516_, uint8_t v_cancel_1517_, lean_object* v_fst_1518_, lean_object* v_inst_1519_, lean_object* v_R_1520_, lean_object* v_a_1521_, lean_object* v_b_1522_, lean_object* v_c_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1517_, v_fst_1518_, v_a_1521_, v_b_1522_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_1530_, lean_object* v_cancel_1531_, lean_object* v_fst_1532_, lean_object* v_inst_1533_, lean_object* v_R_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v_c_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
uint8_t v_cancel_boxed_1543_; lean_object* v_res_1544_; 
v_cancel_boxed_1543_ = lean_unbox(v_cancel_1531_);
v_res_1544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(v_00_u03b1_1530_, v_cancel_boxed_1543_, v_fst_1532_, v_inst_1533_, v_R_1534_, v_a_1535_, v_b_1536_, v_c_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(lean_object* v_00_u03b1_1545_, lean_object* v_msg_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_msg_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(v_00_u03b1_1553_, v_msg_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = l_List_reverse___redArg(v_x_1562_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
else
{
lean_object* v_head_1572_; lean_object* v_tail_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1591_; 
v_head_1572_ = lean_ctor_get(v_x_1561_, 0);
v_tail_1573_ = lean_ctor_get(v_x_1561_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1561_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1575_ = v_x_1561_;
v_isShared_1576_ = v_isSharedCheck_1591_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_tail_1573_);
lean_inc(v_head_1572_);
lean_dec(v_x_1561_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1591_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_head_1572_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v_x_1562_);
lean_ctor_set(v___x_1575_, 0, v_a_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1578_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_x_1562_);
v___x_1580_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
v_x_1561_ = v_tail_1573_;
v_x_1562_ = v___x_1580_;
goto _start;
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_del_object(v___x_1575_);
lean_dec(v_tail_1573_);
lean_dec(v_x_1562_);
v_a_1583_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1577_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1577_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1592_, lean_object* v_x_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1592_, v_x_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(lean_object* v_jobs_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_box(0);
v___x_1611_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1602_, v___x_1610_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1630_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1630_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1630_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v_fst_1617_; lean_object* v_snd_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1629_; 
v___x_1616_ = l_List_unzipTR___redArg(v_a_1612_);
v_fst_1617_ = lean_ctor_get(v___x_1616_, 0);
v_snd_1618_ = lean_ctor_get(v___x_1616_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1620_ = v___x_1616_;
v_isShared_1621_ = v_isSharedCheck_1629_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_snd_1618_);
lean_inc(v_fst_1617_);
lean_dec(v___x_1616_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1629_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1622_, 0, v_fst_1617_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1622_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_snd_1618_);
v___x_1624_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1626_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1624_);
v___x_1626_ = v___x_1614_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
v_a_1631_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1611_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1611_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel(lean_object* v_00_u03b1_1648_, lean_object* v_jobs_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1658_, lean_object* v_jobs_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel(v_00_u03b1_1658_, v_jobs_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1669_, v_x_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(v_00_u03b1_1679_, v_x_1680_, v_x_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg(lean_object* v_jobs_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1707_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1707_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v_snd_1703_; lean_object* v___x_1705_; 
v_snd_1703_ = lean_ctor_get(v_a_1699_, 1);
lean_inc(v_snd_1703_);
lean_dec(v_a_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v_snd_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_snd_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
v_a_1708_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1698_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1698_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg___boxed(lean_object* v_jobs_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter(lean_object* v_00_u03b1_1725_, lean_object* v_jobs_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___boxed(lean_object* v_00_u03b1_1735_, lean_object* v_jobs_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Elab_Term_TermElabM_parIter(v_00_u03b1_1735_, v_jobs_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_box(0);
v___x_1754_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1745_, v___x_1753_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1773_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1757_ = v___x_1754_;
v_isShared_1758_ = v_isSharedCheck_1773_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1754_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1773_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1772_; 
v___x_1759_ = l_List_unzipTR___redArg(v_a_1755_);
v_fst_1760_ = lean_ctor_get(v___x_1759_, 0);
v_snd_1761_ = lean_ctor_get(v___x_1759_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1763_ = v___x_1759_;
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snd_1761_);
lean_inc(v_fst_1760_);
lean_dec(v___x_1759_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1765_, 0, v_fst_1760_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1765_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_snd_1761_);
v___x_1767_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1767_);
v___x_1769_ = v___x_1757_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
v_a_1774_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1754_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1754_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
lean_dec(v_a_1788_);
lean_dec_ref(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1791_, lean_object* v_jobs_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_jobs_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(v_00_u03b1_1801_, v_jobs_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(lean_object* v_jobs_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_snd_1824_; lean_object* v___x_1826_; 
v_snd_1824_ = lean_ctor_get(v_a_1820_, 1);
lean_inc(v_snd_1824_);
lean_dec(v_a_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v_snd_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_snd_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1819_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1819_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy(lean_object* v_00_u03b1_1846_, lean_object* v_jobs_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___boxed(lean_object* v_00_u03b1_1856_, lean_object* v_jobs_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_Elab_Term_TermElabM_parIterGreedy(v_00_u03b1_1856_, v_jobs_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = l_List_reverse___redArg(v_x_1867_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
return v___x_1876_;
}
else
{
lean_object* v_head_1877_; lean_object* v_tail_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1896_; 
v_head_1877_ = lean_ctor_get(v_x_1866_, 0);
v_tail_1878_ = lean_ctor_get(v_x_1866_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1866_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1880_ = v_x_1866_;
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_tail_1878_);
lean_inc(v_head_1877_);
lean_dec(v_x_1866_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_head_1877_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 1, v_x_1867_);
lean_ctor_set(v___x_1880_, 0, v_a_1883_);
v___x_1885_ = v___x_1880_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1883_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_x_1867_);
v___x_1885_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
v_x_1866_ = v_tail_1878_;
v_x_1867_ = v___x_1885_;
goto _start;
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_del_object(v___x_1880_);
lean_dec(v_tail_1878_);
lean_dec(v_x_1867_);
v_a_1888_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1882_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1882_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg___boxed(lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_1897_, v_x_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(lean_object* v_as_x27_1907_, lean_object* v_b_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
if (lean_obj_tag(v_as_x27_1907_) == 0)
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_b_1908_);
return v___x_1916_;
}
else
{
lean_object* v_head_1917_; lean_object* v_tail_1918_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v_a_1927_; lean_object* v___x_2989__overap_1930_; lean_object* v___x_1931_; 
v_head_1917_ = lean_ctor_get(v_as_x27_1907_, 0);
v_tail_1918_ = lean_ctor_get(v_as_x27_1907_, 1);
lean_inc(v_head_1917_);
v___x_2989__overap_1930_ = lean_task_get_own(v_head_1917_);
lean_inc(v___y_1914_);
lean_inc_ref(v___y_1913_);
lean_inc(v___y_1912_);
lean_inc_ref(v___y_1911_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
v___x_1931_ = lean_apply_7(v___x_2989__overap_1930_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, lean_box(0));
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_Elab_Term_saveState___redArg(v___y_1910_, v___y_1912_, v___y_1914_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1944_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1944_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1944_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1932_);
lean_ctor_set(v___x_1938_, 1, v_a_1934_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 1);
lean_ctor_set(v___x_1936_, 0, v___x_1938_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v_b_1908_);
v_as_x27_1907_ = v_tail_1918_;
v_b_1908_ = v___x_1941_;
goto _start;
}
}
}
else
{
lean_object* v_a_1945_; 
lean_dec(v_a_1932_);
v_a_1945_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1933_, 1);
v_a_1927_ = v_a_1945_;
goto v___jp_1926_;
}
}
else
{
lean_object* v_a_1946_; 
v_a_1946_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1931_, 1);
v_a_1927_ = v_a_1946_;
goto v___jp_1926_;
}
v___jp_1919_:
{
if (v___y_1921_ == 0)
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___y_1920_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
lean_ctor_set(v___x_1923_, 1, v_b_1908_);
v_as_x27_1907_ = v_tail_1918_;
v_b_1908_ = v___x_1923_;
goto _start;
}
else
{
lean_object* v___x_1925_; 
lean_dec(v_b_1908_);
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___y_1920_);
return v___x_1925_;
}
}
v___jp_1926_:
{
uint8_t v___x_1928_; 
v___x_1928_ = l_Lean_Exception_isInterrupt(v_a_1927_);
if (v___x_1928_ == 0)
{
uint8_t v___x_1929_; 
lean_inc_ref(v_a_1927_);
v___x_1929_ = l_Lean_Exception_isRuntime(v_a_1927_);
v___y_1920_ = v_a_1927_;
v___y_1921_ = v___x_1929_;
goto v___jp_1919_;
}
else
{
v___y_1920_ = v_a_1927_;
v___y_1921_ = v___x_1928_;
goto v___jp_1919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg___boxed(lean_object* v_as_x27_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_1947_, v_b_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v_as_x27_1947_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg(lean_object* v_jobs_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = lean_st_ref_get(v_a_1959_);
v___x_1966_ = lean_box(0);
v___x_1967_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_1957_, v___x_1966_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_a_1968_, v___x_1966_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
lean_dec(v_a_1968_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1979_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1979_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1974_ = lean_st_ref_swap(v_a_1959_, v___x_1965_);
lean_dec(v___x_1974_);
v___x_1975_ = l_List_reverse___redArg(v_a_1970_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1975_);
v___x_1977_ = v___x_1972_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_dec(v___x_1965_);
return v___x_1969_;
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v___x_1965_);
v_a_1980_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1967_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1967_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg___boxed(lean_object* v_jobs_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par(lean_object* v_00_u03b1_1997_, lean_object* v_jobs_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___boxed(lean_object* v_00_u03b1_2007_, lean_object* v_jobs_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_Elab_Term_TermElabM_par(v_00_u03b1_2007_, v_jobs_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(lean_object* v_00_u03b1_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_2018_, v_x_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(v_00_u03b1_2028_, v_x_2029_, v_x_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(lean_object* v_00_u03b1_2039_, lean_object* v_as_2040_, lean_object* v_as_x27_2041_, lean_object* v_b_2042_, lean_object* v_a_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; 
v___x_2051_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_2041_, v_b_2042_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___boxed(lean_object* v_00_u03b1_2052_, lean_object* v_as_2053_, lean_object* v_as_x27_2054_, lean_object* v_b_2055_, lean_object* v_a_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(v_00_u03b1_2052_, v_as_2053_, v_as_x27_2054_, v_b_2055_, v_a_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v_as_x27_2054_);
lean_dec(v_as_2053_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(lean_object* v_as_x27_2065_, lean_object* v_b_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
if (lean_obj_tag(v_as_x27_2065_) == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_b_2066_);
return v___x_2074_;
}
else
{
lean_object* v_head_2075_; lean_object* v_tail_2076_; lean_object* v___x_2599__overap_2077_; lean_object* v___x_2078_; 
v_head_2075_ = lean_ctor_get(v_as_x27_2065_, 0);
v_tail_2076_ = lean_ctor_get(v_as_x27_2065_, 1);
lean_inc(v_head_2075_);
v___x_2599__overap_2077_ = lean_task_get_own(v_head_2075_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v___y_2068_);
lean_inc_ref(v___y_2067_);
v___x_2078_ = lean_apply_7(v___x_2599__overap_2077_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, lean_box(0));
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v_a_2079_);
v___x_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
lean_ctor_set(v___x_2081_, 1, v_b_2066_);
v_as_x27_2065_ = v_tail_2076_;
v_b_2066_ = v___x_2081_;
goto _start;
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2097_; 
v_a_2083_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2085_ = v___x_2078_;
v_isShared_2086_ = v_isSharedCheck_2097_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2078_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2097_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
uint8_t v___y_2088_; uint8_t v___x_2095_; 
v___x_2095_ = l_Lean_Exception_isInterrupt(v_a_2083_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
lean_inc(v_a_2083_);
v___x_2096_ = l_Lean_Exception_isRuntime(v_a_2083_);
v___y_2088_ = v___x_2096_;
goto v___jp_2087_;
}
else
{
v___y_2088_ = v___x_2095_;
goto v___jp_2087_;
}
v___jp_2087_:
{
if (v___y_2088_ == 0)
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_del_object(v___x_2085_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_a_2083_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v_b_2066_);
v_as_x27_2065_ = v_tail_2076_;
v_b_2066_ = v___x_2090_;
goto _start;
}
else
{
lean_object* v___x_2093_; 
lean_dec(v_b_2066_);
if (v_isShared_2086_ == 0)
{
v___x_2093_ = v___x_2085_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2083_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_2098_, lean_object* v_b_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2098_, v_b_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v_as_x27_2098_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg(lean_object* v_jobs_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2116_ = lean_st_ref_get(v_a_2110_);
v___x_2117_ = lean_box(0);
v___x_2118_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_2108_, v___x_2117_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___x_2120_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_a_2119_, v___x_2117_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2119_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2130_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2130_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2130_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2125_ = lean_st_ref_swap(v_a_2110_, v___x_2116_);
lean_dec(v___x_2125_);
v___x_2126_ = l_List_reverse___redArg(v_a_2121_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2126_);
v___x_2128_ = v___x_2123_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
else
{
lean_dec(v___x_2116_);
return v___x_2120_;
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v___x_2116_);
v_a_2131_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2118_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2118_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg___boxed(lean_object* v_jobs_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27(lean_object* v_00_u03b1_2148_, lean_object* v_jobs_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_jobs_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_Elab_Term_TermElabM_par_x27(v_00_u03b1_2158_, v_jobs_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(lean_object* v_00_u03b1_2168_, lean_object* v_as_2169_, lean_object* v_as_x27_2170_, lean_object* v_b_2171_, lean_object* v_a_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2170_, v_b_2171_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_as_2182_, lean_object* v_as_x27_2183_, lean_object* v_b_2184_, lean_object* v_a_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(v_00_u03b1_2181_, v_as_2182_, v_as_x27_2183_, v_b_2184_, v_a_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v_as_x27_2183_);
lean_dec(v_as_2182_);
return v_res_2193_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_box(1);
v___x_2195_ = l_Lean_MessageData_ofFormat(v___x_2194_);
return v___x_2195_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2));
v___x_2200_ = l_Lean_MessageData_ofFormat(v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 0)
{
return v_x_2201_;
}
else
{
lean_object* v_head_2203_; lean_object* v_tail_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2226_; 
v_head_2203_ = lean_ctor_get(v_x_2202_, 0);
v_tail_2204_ = lean_ctor_get(v_x_2202_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_x_2202_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2206_ = v_x_2202_;
v_isShared_2207_ = v_isSharedCheck_2226_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_tail_2204_);
lean_inc(v_head_2203_);
lean_dec(v_x_2202_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2226_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_before_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2224_; 
v_before_2208_ = lean_ctor_get(v_head_2203_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_head_2203_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; 
v_unused_2225_ = lean_ctor_get(v_head_2203_, 1);
lean_dec(v_unused_2225_);
v___x_2210_ = v_head_2203_;
v_isShared_2211_ = v_isSharedCheck_2224_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_before_2208_);
lean_dec(v_head_2203_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2224_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2211_ == 0)
{
lean_ctor_set_tag(v___x_2210_, 7);
lean_ctor_set(v___x_2210_, 1, v___x_2212_);
lean_ctor_set(v___x_2210_, 0, v_x_2201_);
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_x_2201_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2215_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_2207_ == 0)
{
lean_ctor_set_tag(v___x_2206_, 7);
lean_ctor_set(v___x_2206_, 1, v___x_2215_);
lean_ctor_set(v___x_2206_, 0, v___x_2214_);
v___x_2217_ = v___x_2206_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = l_Lean_MessageData_ofSyntax(v_before_2208_);
v___x_2219_ = l_Lean_indentD(v___x_2218_);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2217_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v_x_2201_ = v___x_2220_;
v_x_2202_ = v_tail_2204_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(lean_object* v_opts_2227_, lean_object* v_opt_2228_){
_start:
{
lean_object* v_name_2229_; lean_object* v_defValue_2230_; lean_object* v_map_2231_; lean_object* v___x_2232_; 
v_name_2229_ = lean_ctor_get(v_opt_2228_, 0);
v_defValue_2230_ = lean_ctor_get(v_opt_2228_, 1);
v_map_2231_ = lean_ctor_get(v_opts_2227_, 0);
v___x_2232_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2231_, v_name_2229_);
if (lean_obj_tag(v___x_2232_) == 0)
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_unbox(v_defValue_2230_);
return v___x_2233_;
}
else
{
lean_object* v_val_2234_; 
v_val_2234_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v___x_2232_, 1);
if (lean_obj_tag(v_val_2234_) == 1)
{
uint8_t v_v_2235_; 
v_v_2235_ = lean_ctor_get_uint8(v_val_2234_, 0);
lean_dec_ref_known(v_val_2234_, 0);
return v_v_2235_;
}
else
{
uint8_t v___x_2236_; 
lean_dec(v_val_2234_);
v___x_2236_ = lean_unbox(v_defValue_2230_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2___boxed(lean_object* v_opts_2237_, lean_object* v_opt_2238_){
_start:
{
uint8_t v_res_2239_; lean_object* v_r_2240_; 
v_res_2239_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_opts_2237_, v_opt_2238_);
lean_dec_ref(v_opt_2238_);
lean_dec_ref(v_opts_2237_);
v_r_2240_ = lean_box(v_res_2239_);
return v_r_2240_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1));
v___x_2245_ = l_Lean_MessageData_ofFormat(v___x_2244_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(lean_object* v_msgData_2246_, lean_object* v_macroStack_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2248_);
v___x_2251_ = l_Lean_Elab_pp_macroStack;
v___x_2252_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v___x_2250_, v___x_2251_);
lean_dec_ref(v___x_2250_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; 
lean_dec(v_macroStack_2247_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_msgData_2246_);
return v___x_2253_;
}
else
{
if (lean_obj_tag(v_macroStack_2247_) == 0)
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_msgData_2246_);
return v___x_2254_;
}
else
{
lean_object* v_head_2255_; lean_object* v_after_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2271_; 
v_head_2255_ = lean_ctor_get(v_macroStack_2247_, 0);
lean_inc(v_head_2255_);
v_after_2256_ = lean_ctor_get(v_head_2255_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_head_2255_);
if (v_isSharedCheck_2271_ == 0)
{
lean_object* v_unused_2272_; 
v_unused_2272_ = lean_ctor_get(v_head_2255_, 0);
lean_dec(v_unused_2272_);
v___x_2258_ = v_head_2255_;
v_isShared_2259_ = v_isSharedCheck_2271_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_after_2256_);
lean_dec(v_head_2255_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2271_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2260_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2259_ == 0)
{
lean_ctor_set_tag(v___x_2258_, 7);
lean_ctor_set(v___x_2258_, 1, v___x_2260_);
lean_ctor_set(v___x_2258_, 0, v_msgData_2246_);
v___x_2262_ = v___x_2258_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_msgData_2246_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v_msgData_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2263_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___x_2263_);
v___x_2265_ = l_Lean_MessageData_ofSyntax(v_after_2256_);
v___x_2266_ = l_Lean_indentD(v___x_2265_);
v_msgData_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2267_, 0, v___x_2264_);
lean_ctor_set(v_msgData_2267_, 1, v___x_2266_);
v___x_2268_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(v_msgData_2267_, v_macroStack_2247_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2273_, lean_object* v_macroStack_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2273_, v_macroStack_2274_, v___y_2275_);
lean_dec_ref(v___y_2275_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(lean_object* v_msg_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_ref_2286_; lean_object* v_macroStack_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v_a_2290_; lean_object* v___x_2291_; lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
v_ref_2286_ = lean_ctor_get(v___y_2283_, 2);
v_macroStack_2287_ = lean_ctor_get(v___y_2279_, 1);
v___x_2288_ = l_Lean_Elab_getBetterRef(v_ref_2286_, v_macroStack_2287_);
v___x_2289_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_2278_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2289_);
lean_inc(v_macroStack_2287_);
v___x_2291_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_a_2290_, v_macroStack_2287_, v___y_2283_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2288_);
lean_ctor_set(v___x_2296_, 1, v_a_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set_tag(v___x_2294_, 1);
lean_ctor_set(v___x_2294_, 0, v___x_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_2310_, lean_object* v___x_2311_, lean_object* v_____r_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_a_2310_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v___x_2311_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
v___x_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_2324_, lean_object* v___x_2325_, lean_object* v_____r_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2324_, v___x_2325_, v_____r_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(uint8_t v_cancel_2335_, lean_object* v_fst_2336_, lean_object* v_a_2337_, lean_object* v_b_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
if (lean_obj_tag(v_a_2337_) == 0)
{
lean_object* v___x_2346_; 
lean_dec_ref(v_fst_2336_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v_b_2338_);
return v___x_2346_;
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v_fst_2350_; lean_object* v_snd_2351_; lean_object* v___y_2353_; lean_object* v___x_2373_; 
lean_dec_ref(v_b_2338_);
v___x_2347_ = lean_box(0);
v___x_2348_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2349_ = l_IO_waitAny_x27___redArg(v_a_2337_);
v_fst_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_fst_2350_);
v_snd_2351_ = lean_ctor_get(v___x_2349_, 1);
lean_inc(v_snd_2351_);
lean_dec_ref(v___x_2349_);
lean_inc(v___y_2344_);
lean_inc_ref(v___y_2343_);
lean_inc(v___y_2342_);
lean_inc_ref(v___y_2341_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
v___x_2373_ = lean_apply_7(v_fst_2350_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, lean_box(0));
if (lean_obj_tag(v___x_2373_) == 0)
{
if (v_cancel_2335_ == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2375_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2374_, v___x_2347_, v___x_2347_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
v___y_2353_ = v___x_2375_;
goto v___jp_2352_;
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_a_2376_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2373_, 1);
lean_inc_ref(v_fst_2336_);
v___x_2377_ = lean_apply_1(v_fst_2336_, lean_box(0));
v___x_2378_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2376_, v___x_2347_, v___x_2377_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
v___y_2353_ = v___x_2378_;
goto v___jp_2352_;
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2391_; 
v_a_2379_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2381_ = v___x_2373_;
v_isShared_2382_ = v_isSharedCheck_2391_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2373_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2391_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
uint8_t v___y_2384_; uint8_t v___x_2389_; 
v___x_2389_ = l_Lean_Exception_isInterrupt(v_a_2379_);
if (v___x_2389_ == 0)
{
uint8_t v___x_2390_; 
lean_inc(v_a_2379_);
v___x_2390_ = l_Lean_Exception_isRuntime(v_a_2379_);
v___y_2384_ = v___x_2390_;
goto v___jp_2383_;
}
else
{
v___y_2384_ = v___x_2389_;
goto v___jp_2383_;
}
v___jp_2383_:
{
if (v___y_2384_ == 0)
{
lean_del_object(v___x_2381_);
lean_dec(v_a_2379_);
v_a_2337_ = v_snd_2351_;
v_b_2338_ = v___x_2348_;
goto _start;
}
else
{
lean_object* v___x_2387_; 
lean_dec(v_snd_2351_);
lean_dec_ref(v_fst_2336_);
if (v_isShared_2382_ == 0)
{
v___x_2387_ = v___x_2381_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2379_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
v___jp_2352_:
{
if (lean_obj_tag(v___y_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2364_; 
v_a_2354_ = lean_ctor_get(v___y_2353_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___y_2353_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2356_ = v___y_2353_;
v_isShared_2357_ = v_isSharedCheck_2364_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___y_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2364_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
if (lean_obj_tag(v_a_2354_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; 
lean_dec(v_snd_2351_);
lean_dec_ref(v_fst_2336_);
v_a_2358_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_a_2358_);
lean_dec_ref_known(v_a_2354_, 1);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v_a_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
else
{
lean_object* v_a_2362_; 
lean_del_object(v___x_2356_);
v_a_2362_ = lean_ctor_get(v_a_2354_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v_a_2354_, 1);
v_a_2337_ = v_snd_2351_;
v_b_2338_ = v_a_2362_;
goto _start;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_snd_2351_);
lean_dec_ref(v_fst_2336_);
v_a_2365_ = lean_ctor_get(v___y_2353_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___y_2353_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___y_2353_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___y_2353_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_2392_, lean_object* v_fst_2393_, lean_object* v_a_2394_, lean_object* v_b_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
uint8_t v_cancel_boxed_2403_; lean_object* v_res_2404_; 
v_cancel_boxed_2403_ = lean_unbox(v_cancel_2392_);
v_res_2404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_boxed_2403_, v_fst_2393_, v_a_2394_, v_b_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg(lean_object* v_jobs_2405_, uint8_t v_cancel_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_2405_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v_fst_2416_; lean_object* v_snd_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v_fst_2416_ = lean_ctor_get(v_a_2415_, 0);
lean_inc(v_fst_2416_);
v_snd_2417_ = lean_ctor_get(v_a_2415_, 1);
lean_inc(v_snd_2417_);
lean_dec(v_a_2415_);
v___x_2418_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2419_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2406_, v_fst_2416_, v_snd_2417_, v___x_2418_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2431_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2431_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2431_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_fst_2424_; 
v_fst_2424_ = lean_ctor_get(v_a_2420_, 0);
lean_inc(v_fst_2424_);
lean_dec(v_a_2420_);
if (lean_obj_tag(v_fst_2424_) == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
lean_del_object(v___x_2422_);
v___x_2425_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_2426_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v___x_2425_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
return v___x_2426_;
}
else
{
lean_object* v_val_2427_; lean_object* v___x_2429_; 
v_val_2427_ = lean_ctor_get(v_fst_2424_, 0);
lean_inc(v_val_2427_);
lean_dec_ref_known(v_fst_2424_, 1);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_val_2427_);
v___x_2429_ = v___x_2422_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_val_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2419_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2419_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2414_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2414_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg___boxed(lean_object* v_jobs_2448_, lean_object* v_cancel_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
uint8_t v_cancel_boxed_2457_; lean_object* v_res_2458_; 
v_cancel_boxed_2457_ = lean_unbox(v_cancel_2449_);
v_res_2458_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2448_, v_cancel_boxed_2457_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst(lean_object* v_00_u03b1_2459_, lean_object* v_jobs_2460_, uint8_t v_cancel_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2460_, v_cancel_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___boxed(lean_object* v_00_u03b1_2470_, lean_object* v_jobs_2471_, lean_object* v_cancel_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
uint8_t v_cancel_boxed_2480_; lean_object* v_res_2481_; 
v_cancel_boxed_2480_ = lean_unbox(v_cancel_2472_);
v_res_2481_ = l_Lean_Elab_Term_TermElabM_parFirst(v_00_u03b1_2470_, v_jobs_2471_, v_cancel_boxed_2480_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(lean_object* v_00_u03b1_2482_, uint8_t v_cancel_2483_, lean_object* v_fst_2484_, lean_object* v_inst_2485_, lean_object* v_R_2486_, lean_object* v_a_2487_, lean_object* v_b_2488_, lean_object* v_c_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2483_, v_fst_2484_, v_a_2487_, v_b_2488_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_cancel_2499_, lean_object* v_fst_2500_, lean_object* v_inst_2501_, lean_object* v_R_2502_, lean_object* v_a_2503_, lean_object* v_b_2504_, lean_object* v_c_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
uint8_t v_cancel_boxed_2513_; lean_object* v_res_2514_; 
v_cancel_boxed_2513_ = lean_unbox(v_cancel_2499_);
v_res_2514_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(v_00_u03b1_2498_, v_cancel_boxed_2513_, v_fst_2500_, v_inst_2501_, v_R_2502_, v_a_2503_, v_b_2504_, v_c_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(lean_object* v_00_u03b1_2515_, lean_object* v_msg_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_2525_, lean_object* v_msg_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(v_00_u03b1_2525_, v_msg_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(lean_object* v_msgData_2535_, lean_object* v_macroStack_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2535_, v_macroStack_2536_, v___y_2541_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_2545_, lean_object* v_macroStack_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(v_msgData_2545_, v_macroStack_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(lean_object* v_x_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
if (lean_obj_tag(v_x_2555_) == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = l_List_reverse___redArg(v_x_2556_);
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
else
{
lean_object* v_head_2568_; lean_object* v_tail_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2587_; 
v_head_2568_ = lean_ctor_get(v_x_2555_, 0);
v_tail_2569_ = lean_ctor_get(v_x_2555_, 1);
v_isSharedCheck_2587_ = !lean_is_exclusive(v_x_2555_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2571_ = v_x_2555_;
v_isShared_2572_ = v_isSharedCheck_2587_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_tail_2569_);
lean_inc(v_head_2568_);
lean_dec(v_x_2555_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2587_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_head_2568_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2576_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v_x_2556_);
lean_ctor_set(v___x_2571_, 0, v_a_2574_);
v___x_2576_ = v___x_2571_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2574_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_x_2556_);
v___x_2576_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
v_x_2555_ = v_tail_2569_;
v_x_2556_ = v___x_2576_;
goto _start;
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_del_object(v___x_2571_);
lean_dec(v_tail_2569_);
lean_dec(v_x_2556_);
v_a_2579_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2573_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2573_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_2588_, lean_object* v_x_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2588_, v_x_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(lean_object* v_jobs_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_box(0);
v___x_2611_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2600_, v___x_2610_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2630_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2630_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2629_; 
v___x_2616_ = l_List_unzipTR___redArg(v_a_2612_);
v_fst_2617_ = lean_ctor_get(v___x_2616_, 0);
v_snd_2618_ = lean_ctor_get(v___x_2616_, 1);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2620_ = v___x_2616_;
v_isShared_2621_ = v_isSharedCheck_2629_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_snd_2618_);
lean_inc(v_fst_2617_);
lean_dec(v___x_2616_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2629_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2622_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2622_, 0, v_fst_2617_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2624_ = v___x_2620_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v_snd_2618_);
v___x_2624_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2624_);
v___x_2626_ = v___x_2614_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
v_a_2631_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2611_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2611_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel(lean_object* v_00_u03b1_2650_, lean_object* v_jobs_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___boxed(lean_object* v_00_u03b1_2662_, lean_object* v_jobs_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel(v_00_u03b1_2662_, v_jobs_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2675_, v_x_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(v_00_u03b1_2687_, v_x_2688_, v_x_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg(lean_object* v_jobs_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2719_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2713_ = v___x_2710_;
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2710_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_snd_2715_; lean_object* v___x_2717_; 
v_snd_2715_ = lean_ctor_get(v_a_2711_, 1);
lean_inc(v_snd_2715_);
lean_dec(v_a_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v_snd_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_snd_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
v_a_2720_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2710_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2710_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg___boxed(lean_object* v_jobs_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter(lean_object* v_00_u03b1_2739_, lean_object* v_jobs_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_jobs_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Elab_Tactic_TacticM_parIter(v_00_u03b1_2751_, v_jobs_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
lean_dec(v_a_2758_);
lean_dec_ref(v_a_2757_);
lean_dec(v_a_2756_);
lean_dec_ref(v_a_2755_);
lean_dec(v_a_2754_);
lean_dec_ref(v_a_2753_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2763_, v___x_2773_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2793_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2793_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2793_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2779_; lean_object* v_fst_2780_; lean_object* v_snd_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2792_; 
v___x_2779_ = l_List_unzipTR___redArg(v_a_2775_);
v_fst_2780_ = lean_ctor_get(v___x_2779_, 0);
v_snd_2781_ = lean_ctor_get(v___x_2779_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2783_ = v___x_2779_;
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_snd_2781_);
lean_inc(v_fst_2780_);
lean_dec(v___x_2779_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2792_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2785_, 0, v_fst_2780_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2785_);
v___x_2787_ = v___x_2783_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_snd_2781_);
v___x_2787_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2789_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2787_);
v___x_2789_ = v___x_2777_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_a_2794_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2774_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2774_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(lean_object* v_00_u03b1_2813_, lean_object* v_jobs_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_2825_, lean_object* v_jobs_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(v_00_u03b1_2825_, v_jobs_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
lean_dec(v_a_2834_);
lean_dec_ref(v_a_2833_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(lean_object* v_jobs_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2856_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2856_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v_snd_2852_; lean_object* v___x_2854_; 
v_snd_2852_ = lean_ctor_get(v_a_2848_, 1);
lean_inc(v_snd_2852_);
lean_dec(v_a_2848_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v_snd_2852_);
v___x_2854_ = v___x_2850_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_snd_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
v_a_2857_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2847_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2847_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg___boxed(lean_object* v_jobs_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec_ref(v_a_2866_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy(lean_object* v_00_u03b1_2876_, lean_object* v_jobs_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___boxed(lean_object* v_00_u03b1_2888_, lean_object* v_jobs_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy(v_00_u03b1_2888_, v_jobs_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(lean_object* v_as_x27_2900_, lean_object* v_b_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
if (lean_obj_tag(v_as_x27_2900_) == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2911_, 0, v_b_2901_);
return v___x_2911_;
}
else
{
lean_object* v_head_2912_; lean_object* v_tail_2913_; lean_object* v___x_2914_; 
v_head_2912_ = lean_ctor_get(v_as_x27_2900_, 0);
v_tail_2913_ = lean_ctor_get(v_as_x27_2900_, 1);
v___x_2914_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2903_, v___y_2905_, v___y_2907_, v___y_2909_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2958_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2958_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2958_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___y_2920_; uint8_t v___y_2921_; lean_object* v_a_2938_; lean_object* v___x_2677__overap_2941_; lean_object* v___x_2942_; 
lean_inc(v_head_2912_);
v___x_2677__overap_2941_ = lean_task_get_own(v_head_2912_);
lean_inc(v___y_2909_);
lean_inc_ref(v___y_2908_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
lean_inc(v___y_2903_);
lean_inc_ref(v___y_2902_);
v___x_2942_ = lean_apply_9(v___x_2677__overap_2941_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, lean_box(0));
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; lean_object* v___x_2944_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v___x_2944_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2903_, v___y_2905_, v___y_2907_, v___y_2909_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2955_; 
lean_del_object(v___x_2917_);
lean_dec(v_a_2915_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2955_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2955_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2949_, 0, v_a_2943_);
lean_ctor_set(v___x_2949_, 1, v_a_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 1);
lean_ctor_set(v___x_2947_, 0, v___x_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2949_);
v___x_2951_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
lean_ctor_set(v___x_2952_, 1, v_b_2901_);
v_as_x27_2900_ = v_tail_2913_;
v_b_2901_ = v___x_2952_;
goto _start;
}
}
}
else
{
lean_object* v_a_2956_; 
lean_dec(v_a_2943_);
v_a_2956_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2944_, 1);
v_a_2938_ = v_a_2956_;
goto v___jp_2937_;
}
}
else
{
lean_object* v_a_2957_; 
v_a_2957_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2942_, 1);
v_a_2938_ = v_a_2957_;
goto v___jp_2937_;
}
v___jp_2919_:
{
if (v___y_2921_ == 0)
{
lean_object* v___x_2922_; 
lean_del_object(v___x_2917_);
v___x_2922_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2915_, v___y_2921_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
lean_dec_ref_known(v___x_2922_, 1);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___y_2920_);
v___x_2924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
lean_ctor_set(v___x_2924_, 1, v_b_2901_);
v_as_x27_2900_ = v_tail_2913_;
v_b_2901_ = v___x_2924_;
goto _start;
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec_ref(v___y_2920_);
lean_dec(v_b_2901_);
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
lean_dec(v_a_2915_);
lean_dec(v_b_2901_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set_tag(v___x_2917_, 1);
lean_ctor_set(v___x_2917_, 0, v___y_2920_);
v___x_2935_ = v___x_2917_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___y_2920_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
v___jp_2937_:
{
uint8_t v___x_2939_; 
v___x_2939_ = l_Lean_Exception_isInterrupt(v_a_2938_);
if (v___x_2939_ == 0)
{
uint8_t v___x_2940_; 
lean_inc_ref(v_a_2938_);
v___x_2940_ = l_Lean_Exception_isRuntime(v_a_2938_);
v___y_2920_ = v_a_2938_;
v___y_2921_ = v___x_2940_;
goto v___jp_2919_;
}
else
{
v___y_2920_ = v_a_2938_;
v___y_2921_ = v___x_2939_;
goto v___jp_2919_;
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_dec(v_b_2901_);
v_a_2959_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2914_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2914_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg___boxed(lean_object* v_as_x27_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_2967_, v_b_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v_as_x27_2967_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(lean_object* v_x_2979_, lean_object* v_x_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
if (lean_obj_tag(v_x_2979_) == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2990_ = l_List_reverse___redArg(v_x_2980_);
v___x_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
return v___x_2991_;
}
else
{
lean_object* v_head_2992_; lean_object* v_tail_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3011_; 
v_head_2992_ = lean_ctor_get(v_x_2979_, 0);
v_tail_2993_ = lean_ctor_get(v_x_2979_, 1);
v_isSharedCheck_3011_ = !lean_is_exclusive(v_x_2979_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_2995_ = v_x_2979_;
v_isShared_2996_ = v_isSharedCheck_3011_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_tail_2993_);
lean_inc(v_head_2992_);
lean_dec(v_x_2979_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3011_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_head_2992_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_3000_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v_x_2980_);
lean_ctor_set(v___x_2995_, 0, v_a_2998_);
v___x_3000_ = v___x_2995_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2998_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_x_2980_);
v___x_3000_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
v_x_2979_ = v_tail_2993_;
v_x_2980_ = v___x_3000_;
goto _start;
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_del_object(v___x_2995_);
lean_dec(v_tail_2993_);
lean_dec(v_x_2980_);
v_a_3003_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2997_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2997_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg___boxed(lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3012_, v_x_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg(lean_object* v_jobs_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_st_ref_get(v_a_3026_);
v___x_3035_ = lean_box(0);
v___x_3036_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_jobs_3024_, v___x_3035_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3038_; 
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_a_3037_);
lean_dec_ref_known(v___x_3036_, 1);
v___x_3038_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_a_3037_, v___x_3035_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_);
lean_dec(v_a_3037_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3048_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3048_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3048_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_st_ref_swap(v_a_3026_, v___x_3034_);
lean_dec(v___x_3043_);
v___x_3044_ = l_List_reverse___redArg(v_a_3039_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3044_);
v___x_3046_ = v___x_3041_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_dec(v___x_3034_);
return v___x_3038_;
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v___x_3034_);
v_a_3049_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3036_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3036_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg___boxed(lean_object* v_jobs_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_a_3058_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par(lean_object* v_00_u03b1_3068_, lean_object* v_jobs_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___boxed(lean_object* v_00_u03b1_3080_, lean_object* v_jobs_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Elab_Tactic_TacticM_par(v_00_u03b1_3080_, v_jobs_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
lean_dec_ref(v_a_3084_);
lean_dec(v_a_3083_);
lean_dec_ref(v_a_3082_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(lean_object* v_00_u03b1_3092_, lean_object* v_x_3093_, lean_object* v_x_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3093_, v_x_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___boxed(lean_object* v_00_u03b1_3105_, lean_object* v_x_3106_, lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(v_00_u03b1_3105_, v_x_3106_, v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(lean_object* v_00_u03b1_3118_, lean_object* v_as_3119_, lean_object* v_as_x27_3120_, lean_object* v_b_3121_, lean_object* v_a_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v___x_3132_; 
v___x_3132_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_3120_, v_b_3121_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_as_3134_, lean_object* v_as_x27_3135_, lean_object* v_b_3136_, lean_object* v_a_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(v_00_u03b1_3133_, v_as_3134_, v_as_x27_3135_, v_b_3136_, v_a_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
lean_dec(v_as_x27_3135_);
lean_dec(v_as_3134_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(lean_object* v_as_x27_3148_, lean_object* v_b_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
if (lean_obj_tag(v_as_x27_3148_) == 0)
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_b_3149_);
return v___x_3159_;
}
else
{
lean_object* v_head_3160_; lean_object* v_tail_3161_; lean_object* v___x_3162_; 
v_head_3160_ = lean_ctor_get(v_as_x27_3148_, 0);
v_tail_3161_ = lean_ctor_get(v_as_x27_3148_, 1);
v___x_3162_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3151_, v___y_3153_, v___y_3155_, v___y_3157_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_2362__overap_3164_; lean_object* v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref_known(v___x_3162_, 1);
lean_inc(v_head_3160_);
v___x_2362__overap_3164_ = lean_task_get_own(v_head_3160_);
lean_inc(v___y_3157_);
lean_inc_ref(v___y_3156_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
lean_inc(v___y_3151_);
lean_inc_ref(v___y_3150_);
v___x_3165_ = lean_apply_9(v___x_2362__overap_3164_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, lean_box(0));
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
lean_dec(v_a_3163_);
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v___x_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3167_, 0, v_a_3166_);
v___x_3168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v_b_3149_);
v_as_x27_3148_ = v_tail_3161_;
v_b_3149_ = v___x_3168_;
goto _start;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3193_; 
v_a_3170_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3172_ = v___x_3165_;
v_isShared_3173_ = v_isSharedCheck_3193_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3165_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3193_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
uint8_t v___y_3175_; uint8_t v___x_3191_; 
v___x_3191_ = l_Lean_Exception_isInterrupt(v_a_3170_);
if (v___x_3191_ == 0)
{
uint8_t v___x_3192_; 
lean_inc(v_a_3170_);
v___x_3192_ = l_Lean_Exception_isRuntime(v_a_3170_);
v___y_3175_ = v___x_3192_;
goto v___jp_3174_;
}
else
{
v___y_3175_ = v___x_3191_;
goto v___jp_3174_;
}
v___jp_3174_:
{
if (v___y_3175_ == 0)
{
lean_object* v___x_3176_; 
lean_del_object(v___x_3172_);
v___x_3176_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3163_, v___y_3175_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_dec_ref_known(v___x_3176_, 1);
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v_a_3170_);
v___x_3178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v_b_3149_);
v_as_x27_3148_ = v_tail_3161_;
v_b_3149_ = v___x_3178_;
goto _start;
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_a_3170_);
lean_dec(v_b_3149_);
v_a_3180_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3176_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3176_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
else
{
lean_object* v___x_3189_; 
lean_dec(v_a_3163_);
lean_dec(v_b_3149_);
if (v_isShared_3173_ == 0)
{
v___x_3189_ = v___x_3172_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3170_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v_b_3149_);
v_a_3194_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3162_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3162_);
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
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3410_; 
v_a_3389_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3391_ = v___x_3383_;
v_isShared_3392_ = v_isSharedCheck_3410_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3383_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3410_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
uint8_t v___y_3394_; uint8_t v___x_3408_; 
v___x_3408_ = l_Lean_Exception_isInterrupt(v_a_3389_);
if (v___x_3408_ == 0)
{
uint8_t v___x_3409_; 
lean_inc(v_a_3389_);
v___x_3409_ = l_Lean_Exception_isRuntime(v_a_3389_);
v___y_3394_ = v___x_3409_;
goto v___jp_3393_;
}
else
{
v___y_3394_ = v___x_3408_;
goto v___jp_3393_;
}
v___jp_3393_:
{
if (v___y_3394_ == 0)
{
lean_object* v___x_3395_; 
lean_del_object(v___x_3391_);
lean_dec(v_a_3389_);
v___x_3395_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3382_, v___y_3394_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
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
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_snd_3359_);
lean_dec(v_fst_3358_);
lean_dec_ref(v_fst_3342_);
v_a_3411_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3381_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3381_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_3419_, lean_object* v_fst_3420_, lean_object* v_a_3421_, lean_object* v_b_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
uint8_t v_cancel_boxed_3432_; lean_object* v_res_3433_; 
v_cancel_boxed_3432_ = lean_unbox(v_cancel_3419_);
v_res_3433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_boxed_3432_, v_fst_3420_, v_a_3421_, v_b_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(lean_object* v_msg_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_ref_3440_; lean_object* v___x_3441_; lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3450_; 
v_ref_3440_ = lean_ctor_get(v___y_3437_, 2);
v___x_3441_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3450_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3446_; lean_object* v___x_3448_; 
lean_inc(v_ref_3440_);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_ref_3440_);
lean_ctor_set(v___x_3446_, 1, v_a_3442_);
if (v_isShared_3445_ == 0)
{
lean_ctor_set_tag(v___x_3444_, 1);
lean_ctor_set(v___x_3444_, 0, v___x_3446_);
v___x_3448_ = v___x_3444_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg(lean_object* v_jobs_3458_, uint8_t v_cancel_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_3458_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v_fst_3471_; lean_object* v_snd_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v_fst_3471_ = lean_ctor_get(v_a_3470_, 0);
lean_inc(v_fst_3471_);
v_snd_3472_ = lean_ctor_get(v_a_3470_, 1);
lean_inc(v_snd_3472_);
lean_dec(v_a_3470_);
v___x_3473_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_3474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3459_, v_fst_3471_, v_snd_3472_, v___x_3473_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3486_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3477_ = v___x_3474_;
v_isShared_3478_ = v_isSharedCheck_3486_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3486_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v_fst_3479_; 
v_fst_3479_ = lean_ctor_get(v_a_3475_, 0);
lean_inc(v_fst_3479_);
lean_dec(v_a_3475_);
if (lean_obj_tag(v_fst_3479_) == 0)
{
lean_object* v___x_3480_; lean_object* v___x_3481_; 
lean_del_object(v___x_3477_);
v___x_3480_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_3481_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v___x_3480_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
return v___x_3481_;
}
else
{
lean_object* v_val_3482_; lean_object* v___x_3484_; 
v_val_3482_ = lean_ctor_get(v_fst_3479_, 0);
lean_inc(v_val_3482_);
lean_dec_ref_known(v_fst_3479_, 1);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 0, v_val_3482_);
v___x_3484_ = v___x_3477_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_val_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
v_a_3487_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3474_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3474_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
v_a_3495_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3469_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3469_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg___boxed(lean_object* v_jobs_3503_, lean_object* v_cancel_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
uint8_t v_cancel_boxed_3514_; lean_object* v_res_3515_; 
v_cancel_boxed_3514_ = lean_unbox(v_cancel_3504_);
v_res_3515_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3503_, v_cancel_boxed_3514_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
lean_dec(v_a_3506_);
lean_dec_ref(v_a_3505_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst(lean_object* v_00_u03b1_3516_, lean_object* v_jobs_3517_, uint8_t v_cancel_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3517_, v_cancel_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___boxed(lean_object* v_00_u03b1_3529_, lean_object* v_jobs_3530_, lean_object* v_cancel_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
uint8_t v_cancel_boxed_3541_; lean_object* v_res_3542_; 
v_cancel_boxed_3541_ = lean_unbox(v_cancel_3531_);
v_res_3542_ = l_Lean_Elab_Tactic_TacticM_parFirst(v_00_u03b1_3529_, v_jobs_3530_, v_cancel_boxed_3541_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
return v_res_3542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(lean_object* v_00_u03b1_3543_, uint8_t v_cancel_3544_, lean_object* v_fst_3545_, lean_object* v_inst_3546_, lean_object* v_R_3547_, lean_object* v_a_3548_, lean_object* v_b_3549_, lean_object* v_c_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3544_, v_fst_3545_, v_a_3548_, v_b_3549_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_3561_ = _args[0];
lean_object* v_cancel_3562_ = _args[1];
lean_object* v_fst_3563_ = _args[2];
lean_object* v_inst_3564_ = _args[3];
lean_object* v_R_3565_ = _args[4];
lean_object* v_a_3566_ = _args[5];
lean_object* v_b_3567_ = _args[6];
lean_object* v_c_3568_ = _args[7];
lean_object* v___y_3569_ = _args[8];
lean_object* v___y_3570_ = _args[9];
lean_object* v___y_3571_ = _args[10];
lean_object* v___y_3572_ = _args[11];
lean_object* v___y_3573_ = _args[12];
lean_object* v___y_3574_ = _args[13];
lean_object* v___y_3575_ = _args[14];
lean_object* v___y_3576_ = _args[15];
lean_object* v___y_3577_ = _args[16];
_start:
{
uint8_t v_cancel_boxed_3578_; lean_object* v_res_3579_; 
v_cancel_boxed_3578_ = lean_unbox(v_cancel_3562_);
v_res_3579_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(v_00_u03b1_3561_, v_cancel_boxed_3578_, v_fst_3563_, v_inst_3564_, v_R_3565_, v_a_3566_, v_b_3567_, v_c_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(lean_object* v_00_u03b1_3580_, lean_object* v_msg_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3581_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_msg_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(v_00_u03b1_3592_, v_msg_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
return v_res_3603_;
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
