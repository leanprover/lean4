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
lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0(lean_object* v_it_1_){
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
LEAN_EXPORT void l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_it_1_ = stack[0].m_obj;
lean_object* v_res_14_;
v_res_14_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0(v_it_1_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0___boxed(lean_object* v_it_15_, lean_object* v___y_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___lam__0(v_it_15_);
return v_res_17_;
}
}
lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg(){
_start:
{
lean_object* v___f_20_; 
v___f_20_ = ((lean_object*)(l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___closed__0));
return v___f_20_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_21_;
v_res_21_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg();
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___boxed(lean_object* v___dummy_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg();
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO(lean_object* v_00_u03b1_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = ((lean_object*)(l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_Internal_instIteratorTaskIteratorBaseIO___redArg___closed__0));
return v___f_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(lean_object* v_tasks_26_){
_start:
{
lean_inc(v_tasks_26_);
return v_tasks_26_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg___boxed(lean_object* v_tasks_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(v_tasks_27_);
lean_dec(v_tasks_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks(lean_object* v_00_u03b1_29_, lean_object* v_tasks_30_){
_start:
{
lean_inc(v_tasks_30_);
return v_tasks_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___boxed(lean_object* v_00_u03b1_31_, lean_object* v_tasks_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks(v_00_u03b1_31_, v_tasks_32_);
lean_dec(v_tasks_32_);
return v_res_33_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = l_List_reverse___redArg(v_x_35_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
else
{
lean_object* v_head_41_; lean_object* v_tail_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_60_; 
v_head_41_ = lean_ctor_get(v_x_34_, 0);
v_tail_42_ = lean_ctor_get(v_x_34_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v_x_34_);
if (v_isSharedCheck_60_ == 0)
{
v___x_44_ = v_x_34_;
v_isShared_45_ = v_isSharedCheck_60_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_tail_42_);
lean_inc(v_head_41_);
lean_dec(v_x_34_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_60_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Core_CoreM_asTask___redArg(v_head_41_, v___y_36_, v___y_37_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_46_, 1);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v_x_35_);
lean_ctor_set(v___x_44_, 0, v_a_47_);
v___x_49_ = v___x_44_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_47_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_x_35_);
v___x_49_ = v_reuseFailAlloc_51_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
v_x_34_ = v_tail_42_;
v_x_35_ = v___x_49_;
goto _start;
}
}
else
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_59_; 
lean_del_object(v___x_44_);
lean_dec(v_tail_42_);
lean_dec(v_x_35_);
v_a_52_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_59_ == 0)
{
v___x_54_ = v___x_46_;
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_46_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_59_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_57_; 
if (v_isShared_55_ == 0)
{
v___x_57_ = v___x_54_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_a_52_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_34_ = stack[0].m_obj;
lean_object* v_x_35_ = stack[1].m_obj;
lean_object* v___y_36_ = stack[2].m_obj;
lean_object* v___y_37_ = stack[3].m_obj;
lean_object* v_res_61_;
v_res_61_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_x_34_, v_x_35_, v___y_36_, v___y_37_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_62_, lean_object* v_x_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_x_62_, v_x_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
return v_res_67_;
}
}
lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(lean_object* v_as_68_){
_start:
{
if (lean_obj_tag(v_as_68_) == 0)
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
else
{
lean_object* v_head_71_; lean_object* v_tail_72_; lean_object* v___x_73_; 
v_head_71_ = lean_ctor_get(v_as_68_, 0);
lean_inc(v_head_71_);
v_tail_72_ = lean_ctor_get(v_as_68_, 1);
lean_inc(v_tail_72_);
lean_dec_ref_known(v_as_68_, 2);
v___x_73_ = lean_apply_1(v_head_71_, lean_box(0));
v_as_68_ = v_tail_72_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_68_ = stack[0].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(v_as_68_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed(lean_object* v_as_76_, lean_object* v___y_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(v_as_76_);
return v_res_78_;
}
}
lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg(lean_object* v_jobs_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_box(0);
v___x_84_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_jobs_79_, v___x_83_, v_a_80_, v_a_81_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_103_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_103_ == 0)
{
v___x_87_ = v___x_84_;
v_isShared_88_ = v_isSharedCheck_103_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v___x_84_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_103_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_89_; lean_object* v_fst_90_; lean_object* v_snd_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_102_; 
v___x_89_ = l_List_unzipTR___redArg(v_a_85_);
v_fst_90_ = lean_ctor_get(v___x_89_, 0);
v_snd_91_ = lean_ctor_get(v___x_89_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_102_ == 0)
{
v___x_93_ = v___x_89_;
v_isShared_94_ = v_isSharedCheck_102_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_snd_91_);
lean_inc(v_fst_90_);
lean_dec(v___x_89_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_102_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_95_, 0, v_fst_90_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_95_);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_snd_91_);
v___x_97_ = v_reuseFailAlloc_101_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_99_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 0, v___x_97_);
v___x_99_ = v___x_87_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
v_a_104_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_84_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_84_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIterWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_79_ = stack[0].m_obj;
lean_object* v_a_80_ = stack[1].m_obj;
lean_object* v_a_81_ = stack[2].m_obj;
lean_object* v_res_112_;
v_res_112_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_79_, v_a_80_, v_a_81_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
return v_res_117_;
}
}
lean_object* l_Lean_Core_CoreM_parIterWithCancel(lean_object* v_00_u03b1_118_, lean_object* v_jobs_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_119_, v_a_120_, v_a_121_);
return v___x_123_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIterWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_119_ = stack[1].m_obj;
lean_object* v_a_120_ = stack[2].m_obj;
lean_object* v_a_121_ = stack[3].m_obj;
lean_object* v_res_124_;
v_res_124_ = l_Lean_Core_CoreM_parIterWithCancel(lean_box(0), v_jobs_119_, v_a_120_, v_a_121_);
stack->m_obj
 = v_res_124_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___boxed(lean_object* v_00_u03b1_125_, lean_object* v_jobs_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Core_CoreM_parIterWithCancel(v_00_u03b1_125_, v_jobs_126_, v_a_127_, v_a_128_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
return v_res_130_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_131_, lean_object* v_x_132_, lean_object* v_x_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_x_132_, v_x_133_, v___y_134_, v___y_135_);
return v___x_137_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_132_ = stack[1].m_obj;
lean_object* v_x_133_ = stack[2].m_obj;
lean_object* v___y_134_ = stack[3].m_obj;
lean_object* v___y_135_ = stack[4].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(lean_box(0), v_x_132_, v_x_133_, v___y_134_, v___y_135_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_139_, lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(v_00_u03b1_139_, v_x_140_, v_x_141_, v___y_142_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_145_;
}
}
lean_object* l_Lean_Core_CoreM_parIter___redArg(lean_object* v_jobs_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_146_, v_a_147_, v_a_148_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_159_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_159_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_159_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v_snd_155_; lean_object* v___x_157_; 
v_snd_155_ = lean_ctor_get(v_a_151_, 1);
lean_inc(v_snd_155_);
lean_dec(v_a_151_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v_snd_155_);
v___x_157_ = v___x_153_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_snd_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_150_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_150_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_146_ = stack[0].m_obj;
lean_object* v_a_147_ = stack[1].m_obj;
lean_object* v_a_148_ = stack[2].m_obj;
lean_object* v_res_168_;
v_res_168_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_146_, v_a_147_, v_a_148_);
stack->m_obj
 = v_res_168_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___redArg___boxed(lean_object* v_jobs_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_173_;
}
}
lean_object* l_Lean_Core_CoreM_parIter(lean_object* v_00_u03b1_174_, lean_object* v_jobs_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_175_, v_a_176_, v_a_177_);
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIter_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_175_ = stack[1].m_obj;
lean_object* v_a_176_ = stack[2].m_obj;
lean_object* v_a_177_ = stack[3].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_Core_CoreM_parIter(lean_box(0), v_jobs_175_, v_a_176_, v_a_177_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___boxed(lean_object* v_00_u03b1_181_, lean_object* v_jobs_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Core_CoreM_parIter(v_00_u03b1_181_, v_jobs_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_186_;
}
}
lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_box(0);
v___x_192_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_jobs_187_, v___x_191_, v_a_188_, v_a_189_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_211_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_211_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_211_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_211_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_210_; 
v___x_197_ = l_List_unzipTR___redArg(v_a_193_);
v_fst_198_ = lean_ctor_get(v___x_197_, 0);
v_snd_199_ = lean_ctor_get(v___x_197_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_210_ == 0)
{
v___x_201_ = v___x_197_;
v_isShared_202_ = v_isSharedCheck_210_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_snd_199_);
lean_inc(v_fst_198_);
lean_dec(v___x_197_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_210_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_203_, 0, v_fst_198_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_203_);
v___x_205_ = v___x_201_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_snd_199_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_207_; 
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_205_);
v___x_207_ = v___x_195_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
v_a_212_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_192_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_192_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_187_ = stack[0].m_obj;
lean_object* v_a_188_ = stack[1].m_obj;
lean_object* v_a_189_ = stack[2].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_187_, v_a_188_, v_a_189_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_225_;
}
}
lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel(lean_object* v_00_u03b1_226_, lean_object* v_jobs_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_227_, v_a_228_, v_a_229_);
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIterGreedyWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_227_ = stack[1].m_obj;
lean_object* v_a_228_ = stack[2].m_obj;
lean_object* v_a_229_ = stack[3].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_Lean_Core_CoreM_parIterGreedyWithCancel(lean_box(0), v_jobs_227_, v_a_228_, v_a_229_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_233_, lean_object* v_jobs_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Core_CoreM_parIterGreedyWithCancel(v_00_u03b1_233_, v_jobs_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_238_;
}
}
lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg(lean_object* v_jobs_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_239_, v_a_240_, v_a_241_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_snd_248_; lean_object* v___x_250_; 
v_snd_248_ = lean_ctor_get(v_a_244_, 1);
lean_inc(v_snd_248_);
lean_dec(v_a_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v_snd_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_snd_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
v_a_253_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_243_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_243_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIterGreedy___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_239_ = stack[0].m_obj;
lean_object* v_a_240_ = stack[1].m_obj;
lean_object* v_a_241_ = stack[2].m_obj;
lean_object* v_res_261_;
v_res_261_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_239_, v_a_240_, v_a_241_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg___boxed(lean_object* v_jobs_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
return v_res_266_;
}
}
lean_object* l_Lean_Core_CoreM_parIterGreedy(lean_object* v_00_u03b1_267_, lean_object* v_jobs_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_268_, v_a_269_, v_a_270_);
return v___x_272_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parIterGreedy_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_268_ = stack[1].m_obj;
lean_object* v_a_269_ = stack[2].m_obj;
lean_object* v_a_270_ = stack[3].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Lean_Core_CoreM_parIterGreedy(lean_box(0), v_jobs_268_, v_a_269_, v_a_270_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___boxed(lean_object* v_00_u03b1_274_, lean_object* v_jobs_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Core_CoreM_parIterGreedy(v_00_u03b1_274_, v_jobs_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
return v_res_279_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(lean_object* v_as_x27_280_, lean_object* v_b_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
if (lean_obj_tag(v_as_x27_280_) == 0)
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v_b_281_);
return v___x_285_;
}
else
{
lean_object* v_head_286_; lean_object* v_tail_287_; lean_object* v_a_289_; lean_object* v___y_293_; uint8_t v___y_294_; lean_object* v_a_298_; lean_object* v___x_1808__overap_301_; lean_object* v___x_302_; 
v_head_286_ = lean_ctor_get(v_as_x27_280_, 0);
v_tail_287_ = lean_ctor_get(v_as_x27_280_, 1);
lean_inc(v_head_286_);
v___x_1808__overap_301_ = lean_task_get_own(v_head_286_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
v___x_302_ = lean_apply_3(v___x_1808__overap_301_, v___y_282_, v___y_283_, lean_box(0));
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v___x_304_ = l_Lean_Core_saveState___redArg(v___y_283_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_313_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_313_ == 0)
{
v___x_307_ = v___x_304_;
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_313_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_311_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_a_303_);
lean_ctor_set(v___x_309_, 1, v_a_305_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 1);
lean_ctor_set(v___x_307_, 0, v___x_309_);
v___x_311_ = v___x_307_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
v_a_289_ = v___x_311_;
goto v___jp_288_;
}
}
}
else
{
lean_object* v_a_314_; 
lean_dec(v_a_303_);
v_a_314_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_304_, 1);
v_a_298_ = v_a_314_;
goto v___jp_297_;
}
}
else
{
lean_object* v_a_315_; 
v_a_315_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_302_, 1);
v_a_298_ = v_a_315_;
goto v___jp_297_;
}
v___jp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_290_, 0, v_a_289_);
lean_ctor_set(v___x_290_, 1, v_b_281_);
v_as_x27_280_ = v_tail_287_;
v_b_281_ = v___x_290_;
goto _start;
}
v___jp_292_:
{
if (v___y_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___y_293_);
v_a_289_ = v___x_295_;
goto v___jp_288_;
}
else
{
lean_object* v___x_296_; 
lean_dec(v_b_281_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v___y_293_);
return v___x_296_;
}
}
v___jp_297_:
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_Exception_isInterrupt(v_a_298_);
if (v___x_299_ == 0)
{
uint8_t v___x_300_; 
lean_inc_ref(v_a_298_);
v___x_300_ = l_Lean_Exception_isRuntime(v_a_298_);
v___y_293_ = v_a_298_;
v___y_294_ = v___x_300_;
goto v___jp_292_;
}
else
{
v___y_293_ = v_a_298_;
v___y_294_ = v___x_299_;
goto v___jp_292_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_280_ = stack[0].m_obj;
lean_object* v_b_281_ = stack[1].m_obj;
lean_object* v___y_282_ = stack[2].m_obj;
lean_object* v___y_283_ = stack[3].m_obj;
lean_object* v_res_316_;
v_res_316_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_280_, v_b_281_, v___y_282_, v___y_283_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg___boxed(lean_object* v_as_x27_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_317_, v_b_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v_as_x27_317_);
return v_res_322_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = l_List_reverse___redArg(v_x_324_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
else
{
lean_object* v_head_330_; lean_object* v_tail_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_349_; 
v_head_330_ = lean_ctor_get(v_x_323_, 0);
v_tail_331_ = lean_ctor_get(v_x_323_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_349_ == 0)
{
v___x_333_ = v_x_323_;
v_isShared_334_ = v_isSharedCheck_349_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_tail_331_);
lean_inc(v_head_330_);
lean_dec(v_x_323_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_349_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_head_330_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_338_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_x_324_);
lean_ctor_set(v___x_333_, 0, v_a_336_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_x_324_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
v_x_323_ = v_tail_331_;
v_x_324_ = v___x_338_;
goto _start;
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_del_object(v___x_333_);
lean_dec(v_tail_331_);
lean_dec(v_x_324_);
v_a_341_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_335_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_335_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_323_ = stack[0].m_obj;
lean_object* v_x_324_ = stack[1].m_obj;
lean_object* v___y_325_ = stack[2].m_obj;
lean_object* v___y_326_ = stack[3].m_obj;
lean_object* v_res_350_;
v_res_350_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_323_, v_x_324_, v___y_325_, v___y_326_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg___boxed(lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_351_, v_x_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_356_;
}
}
lean_object* l_Lean_Core_CoreM_par___redArg(lean_object* v_jobs_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_st_ref_get(v_a_359_);
v___x_362_ = lean_box(0);
v___x_363_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_357_, v___x_362_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; lean_object* v___x_365_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_a_364_, v___x_362_, v_a_358_, v_a_359_);
lean_dec(v_a_364_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_375_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_375_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = lean_st_ref_swap(v_a_359_, v___x_361_);
lean_dec(v___x_370_);
v___x_371_ = l_List_reverse___redArg(v_a_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_dec(v___x_361_);
return v___x_365_;
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v___x_361_);
v_a_376_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_363_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_363_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_par___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_357_ = stack[0].m_obj;
lean_object* v_a_358_ = stack[1].m_obj;
lean_object* v_a_359_ = stack[2].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Lean_Core_CoreM_par___redArg(v_jobs_357_, v_a_358_, v_a_359_);
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg___boxed(lean_object* v_jobs_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Core_CoreM_par___redArg(v_jobs_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_389_;
}
}
lean_object* l_Lean_Core_CoreM_par(lean_object* v_00_u03b1_390_, lean_object* v_jobs_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Core_CoreM_par___redArg(v_jobs_391_, v_a_392_, v_a_393_);
return v___x_395_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_par_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_391_ = stack[1].m_obj;
lean_object* v_a_392_ = stack[2].m_obj;
lean_object* v_a_393_ = stack[3].m_obj;
lean_object* v_res_396_;
v_res_396_ = l_Lean_Core_CoreM_par(lean_box(0), v_jobs_391_, v_a_392_, v_a_393_);
stack->m_obj
 = v_res_396_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___boxed(lean_object* v_00_u03b1_397_, lean_object* v_jobs_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Core_CoreM_par(v_00_u03b1_397_, v_jobs_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_402_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(lean_object* v_00_u03b1_403_, lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_404_, v_x_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_404_ = stack[1].m_obj;
lean_object* v_x_405_ = stack[2].m_obj;
lean_object* v___y_406_ = stack[3].m_obj;
lean_object* v___y_407_ = stack[4].m_obj;
lean_object* v_res_410_;
v_res_410_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(lean_box(0), v_x_404_, v_x_405_, v___y_406_, v___y_407_);
stack->m_obj
 = v_res_410_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___boxed(lean_object* v_00_u03b1_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(v_00_u03b1_411_, v_x_412_, v_x_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_417_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(lean_object* v_00_u03b1_418_, lean_object* v_as_419_, lean_object* v_as_x27_420_, lean_object* v_b_421_, lean_object* v_a_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_420_, v_b_421_, v___y_423_, v___y_424_);
return v___x_426_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_419_ = stack[1].m_obj;
lean_object* v_as_x27_420_ = stack[2].m_obj;
lean_object* v_b_421_ = stack[3].m_obj;
lean_object* v___y_423_ = stack[5].m_obj;
lean_object* v___y_424_ = stack[6].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(lean_box(0), v_as_419_, v_as_x27_420_, v_b_421_, lean_box(0), v___y_423_, v___y_424_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___boxed(lean_object* v_00_u03b1_428_, lean_object* v_as_429_, lean_object* v_as_x27_430_, lean_object* v_b_431_, lean_object* v_a_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(v_00_u03b1_428_, v_as_429_, v_as_x27_430_, v_b_431_, v_a_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v_as_x27_430_);
lean_dec(v_as_429_);
return v_res_436_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(lean_object* v_as_x27_437_, lean_object* v_b_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
if (lean_obj_tag(v_as_x27_437_) == 0)
{
lean_object* v___x_442_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_b_438_);
return v___x_442_;
}
else
{
lean_object* v_head_443_; lean_object* v_tail_444_; lean_object* v___x_1618__overap_445_; lean_object* v___x_446_; 
v_head_443_ = lean_ctor_get(v_as_x27_437_, 0);
v_tail_444_ = lean_ctor_get(v_as_x27_437_, 1);
lean_inc(v_head_443_);
v___x_1618__overap_445_ = lean_task_get_own(v_head_443_);
lean_inc(v___y_440_);
lean_inc_ref(v___y_439_);
v___x_446_ = lean_apply_3(v___x_1618__overap_445_, v___y_439_, v___y_440_, lean_box(0));
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_448_, 0, v_a_447_);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_b_438_);
v_as_x27_437_ = v_tail_444_;
v_b_438_ = v___x_449_;
goto _start;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_465_; 
v_a_451_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_465_ == 0)
{
v___x_453_ = v___x_446_;
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_446_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_465_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
uint8_t v___y_456_; uint8_t v___x_463_; 
v___x_463_ = l_Lean_Exception_isInterrupt(v_a_451_);
if (v___x_463_ == 0)
{
uint8_t v___x_464_; 
lean_inc(v_a_451_);
v___x_464_ = l_Lean_Exception_isRuntime(v_a_451_);
v___y_456_ = v___x_464_;
goto v___jp_455_;
}
else
{
v___y_456_ = v___x_463_;
goto v___jp_455_;
}
v___jp_455_:
{
if (v___y_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_del_object(v___x_453_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_a_451_);
v___x_458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v_b_438_);
v_as_x27_437_ = v_tail_444_;
v_b_438_ = v___x_458_;
goto _start;
}
else
{
lean_object* v___x_461_; 
lean_dec(v_b_438_);
if (v_isShared_454_ == 0)
{
v___x_461_ = v___x_453_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_451_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_437_ = stack[0].m_obj;
lean_object* v_b_438_ = stack[1].m_obj;
lean_object* v___y_439_ = stack[2].m_obj;
lean_object* v___y_440_ = stack[3].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_437_, v_b_438_, v___y_439_, v___y_440_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_467_, v_b_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v_as_x27_467_);
return v_res_472_;
}
}
lean_object* l_Lean_Core_CoreM_par_x27___redArg(lean_object* v_jobs_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_st_ref_get(v_a_475_);
v___x_478_ = lean_box(0);
v___x_479_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_473_, v___x_478_, v_a_474_, v_a_475_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v___x_481_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_a_480_, v___x_478_, v_a_474_, v_a_475_);
lean_dec(v_a_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_491_; 
v_a_482_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_491_ == 0)
{
v___x_484_ = v___x_481_;
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_481_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_491_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_486_ = lean_st_ref_swap(v_a_475_, v___x_477_);
lean_dec(v___x_486_);
v___x_487_ = l_List_reverse___redArg(v_a_482_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 0, v___x_487_);
v___x_489_ = v___x_484_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_dec(v___x_477_);
return v___x_481_;
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v___x_477_);
v_a_492_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_479_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_479_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_par_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_473_ = stack[0].m_obj;
lean_object* v_a_474_ = stack[1].m_obj;
lean_object* v_a_475_ = stack[2].m_obj;
lean_object* v_res_500_;
v_res_500_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_473_, v_a_474_, v_a_475_);
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg___boxed(lean_object* v_jobs_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
return v_res_505_;
}
}
lean_object* l_Lean_Core_CoreM_par_x27(lean_object* v_00_u03b1_506_, lean_object* v_jobs_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_507_, v_a_508_, v_a_509_);
return v___x_511_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_par_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_507_ = stack[1].m_obj;
lean_object* v_a_508_ = stack[2].m_obj;
lean_object* v_a_509_ = stack[3].m_obj;
lean_object* v_res_512_;
v_res_512_ = l_Lean_Core_CoreM_par_x27(lean_box(0), v_jobs_507_, v_a_508_, v_a_509_);
stack->m_obj
 = v_res_512_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___boxed(lean_object* v_00_u03b1_513_, lean_object* v_jobs_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Core_CoreM_par_x27(v_00_u03b1_513_, v_jobs_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
return v_res_518_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(lean_object* v_00_u03b1_519_, lean_object* v_as_520_, lean_object* v_as_x27_521_, lean_object* v_b_522_, lean_object* v_a_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_521_, v_b_522_, v___y_524_, v___y_525_);
return v___x_527_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_520_ = stack[1].m_obj;
lean_object* v_as_x27_521_ = stack[2].m_obj;
lean_object* v_b_522_ = stack[3].m_obj;
lean_object* v___y_524_ = stack[5].m_obj;
lean_object* v___y_525_ = stack[6].m_obj;
lean_object* v_res_528_;
v_res_528_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(lean_box(0), v_as_520_, v_as_x27_521_, v_b_522_, lean_box(0), v___y_524_, v___y_525_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_529_, lean_object* v_as_530_, lean_object* v_as_x27_531_, lean_object* v_b_532_, lean_object* v_a_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(v_00_u03b1_529_, v_as_530_, v_as_x27_531_, v_b_532_, v_a_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v_as_x27_531_);
lean_dec(v_as_530_);
return v_res_537_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_538_, lean_object* v___x_539_, lean_object* v_____r_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_a_538_);
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_539_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_538_ = stack[0].m_obj;
lean_object* v___x_539_ = stack[1].m_obj;
lean_object* v_____r_540_ = stack[2].m_obj;
lean_object* v___y_541_ = stack[3].m_obj;
lean_object* v___y_542_ = stack[4].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_538_, v___x_539_, v_____r_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_549_, lean_object* v___x_550_, lean_object* v_____r_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_549_, v___x_550_, v_____r_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_555_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(uint8_t v_cancel_559_, lean_object* v_fst_560_, lean_object* v_a_561_, lean_object* v_b_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
if (lean_obj_tag(v_a_561_) == 0)
{
lean_object* v___x_566_; 
lean_dec_ref(v_fst_560_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v_b_562_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___y_573_; lean_object* v___x_593_; 
lean_dec_ref(v_b_562_);
v___x_567_ = lean_box(0);
v___x_568_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_569_ = l_IO_waitAny_x27___redArg(v_a_561_);
v_fst_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_fst_570_);
v_snd_571_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_snd_571_);
lean_dec_ref(v___x_569_);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
v___x_593_ = lean_apply_3(v_fst_570_, v___y_563_, v___y_564_, lean_box(0));
if (lean_obj_tag(v___x_593_) == 0)
{
if (v_cancel_559_ == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_594_, v___x_567_, v___x_567_, v___y_563_, v___y_564_);
v___y_573_ = v___x_595_;
goto v___jp_572_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_a_596_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_593_, 1);
lean_inc_ref(v_fst_560_);
v___x_597_ = lean_apply_1(v_fst_560_, lean_box(0));
v___x_598_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_596_, v___x_567_, v___x_597_, v___y_563_, v___y_564_);
v___y_573_ = v___x_598_;
goto v___jp_572_;
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_611_; 
v_a_599_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_601_ = v___x_593_;
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_593_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_611_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___y_604_; uint8_t v___x_609_; 
v___x_609_ = l_Lean_Exception_isInterrupt(v_a_599_);
if (v___x_609_ == 0)
{
uint8_t v___x_610_; 
lean_inc(v_a_599_);
v___x_610_ = l_Lean_Exception_isRuntime(v_a_599_);
v___y_604_ = v___x_610_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_609_;
goto v___jp_603_;
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
lean_del_object(v___x_601_);
lean_dec(v_a_599_);
v_a_561_ = v_snd_571_;
v_b_562_ = v___x_568_;
goto _start;
}
else
{
lean_object* v___x_607_; 
lean_dec(v_snd_571_);
lean_dec_ref(v_fst_560_);
if (v_isShared_602_ == 0)
{
v___x_607_ = v___x_601_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_599_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
v___jp_572_:
{
if (lean_obj_tag(v___y_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_584_; 
v_a_574_ = lean_ctor_get(v___y_573_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___y_573_);
if (v_isSharedCheck_584_ == 0)
{
v___x_576_ = v___y_573_;
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___y_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_584_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
if (lean_obj_tag(v_a_574_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; 
lean_dec(v_snd_571_);
lean_dec_ref(v_fst_560_);
v_a_578_ = lean_ctor_get(v_a_574_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v_a_574_, 1);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v_a_578_);
v___x_580_ = v___x_576_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
else
{
lean_object* v_a_582_; 
lean_del_object(v___x_576_);
v_a_582_ = lean_ctor_get(v_a_574_, 0);
lean_inc(v_a_582_);
lean_dec_ref_known(v_a_574_, 1);
v_a_561_ = v_snd_571_;
v_b_562_ = v_a_582_;
goto _start;
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec(v_snd_571_);
lean_dec_ref(v_fst_560_);
v_a_585_ = lean_ctor_get(v___y_573_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___y_573_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___y_573_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___y_573_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_559_ = stack[0].m_num;
lean_object* v_fst_560_ = stack[1].m_obj;
lean_object* v_a_561_ = stack[2].m_obj;
lean_object* v_b_562_ = stack[3].m_obj;
lean_object* v___y_563_ = stack[4].m_obj;
lean_object* v___y_564_ = stack[5].m_obj;
lean_object* v_res_612_;
v_res_612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_559_, v_fst_560_, v_a_561_, v_b_562_, v___y_563_, v___y_564_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_613_, lean_object* v_fst_614_, lean_object* v_a_615_, lean_object* v_b_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
uint8_t v_cancel_boxed_620_; lean_object* v_res_621_; 
v_cancel_boxed_620_ = lean_unbox(v_cancel_613_);
v_res_621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_boxed_620_, v_fst_614_, v_a_615_, v_b_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_622_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_625_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_626_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set(v___x_628_, 3, v___x_627_);
lean_ctor_set(v___x_628_, 4, v___x_626_);
lean_ctor_set(v___x_628_, 5, v___x_626_);
lean_ctor_set(v___x_628_, 6, v___x_626_);
lean_ctor_set(v___x_628_, 7, v___x_626_);
lean_ctor_set(v___x_628_, 8, v___x_626_);
lean_ctor_set(v___x_628_, 9, v___x_626_);
lean_ctor_set(v___x_628_, 10, v___x_626_);
lean_ctor_set(v___x_628_, 11, v___x_625_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(32u);
v___x_630_ = lean_mk_empty_array_with_capacity(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_632_ = ((size_t)5ULL);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_unsigned_to_nat(32u);
v___x_635_ = lean_mk_empty_array_with_capacity(v___x_634_);
v___x_636_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3);
v___x_637_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_633_);
lean_ctor_set(v___x_637_, 3, v___x_633_);
lean_ctor_set_usize(v___x_637_, 4, v___x_632_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_638_ = lean_box(1);
v___x_639_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4);
v___x_640_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
lean_ctor_set(v___x_641_, 2, v___x_638_);
return v___x_641_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(lean_object* v_msgData_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v_toCold_647_; lean_object* v_env_648_; lean_object* v_options_649_; uint8_t v___x_650_; lean_object* v_env_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_646_ = lean_st_ref_get(v___y_644_);
v_toCold_647_ = lean_ctor_get(v___y_643_, 0);
v_env_648_ = lean_ctor_get(v___x_646_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_646_);
v_options_649_ = lean_ctor_get(v_toCold_647_, 2);
v___x_650_ = 0;
v_env_651_ = l_Lean_Environment_setRecordingDeps(v_env_648_, v___x_650_);
v___x_652_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2);
v___x_653_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_649_);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v_env_651_);
lean_ctor_set(v___x_654_, 1, v___x_652_);
lean_ctor_set(v___x_654_, 2, v___x_653_);
lean_ctor_set(v___x_654_, 3, v_options_649_);
v___x_655_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_msgData_642_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_642_ = stack[0].m_obj;
lean_object* v___y_643_ = stack[1].m_obj;
lean_object* v___y_644_ = stack[2].m_obj;
lean_object* v_res_657_;
v_res_657_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msgData_642_, v___y_643_, v___y_644_);
stack->m_obj
 = v_res_657_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msgData_658_, v___y_659_, v___y_660_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_662_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_ref_667_; lean_object* v___x_668_; lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_ref_667_ = lean_ctor_get(v___y_664_, 2);
v___x_668_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msg_663_, v___y_664_, v___y_665_);
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
lean_inc(v_ref_667_);
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v_ref_667_);
lean_ctor_set(v___x_673_, 1, v_a_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 1);
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_663_ = stack[0].m_obj;
lean_object* v___y_664_ = stack[1].m_obj;
lean_object* v___y_665_ = stack[2].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_663_, v___y_664_, v___y_665_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_683_;
}
}
static lean_object* _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = ((lean_object*)(l_Lean_Core_CoreM_parFirst___redArg___closed__0));
v___x_686_ = l_Lean_stringToMessageData(v___x_685_);
return v___x_686_;
}
}
lean_object* l_Lean_Core_CoreM_parFirst___redArg(lean_object* v_jobs_687_, uint8_t v_cancel_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_687_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v_fst_694_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_fst_694_);
v_snd_695_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_snd_695_);
lean_dec(v_a_693_);
v___x_696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_697_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_688_, v_fst_694_, v_snd_695_, v___x_696_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_709_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_709_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_709_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_709_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_fst_702_; 
v_fst_702_ = lean_ctor_get(v_a_698_, 0);
lean_inc(v_fst_702_);
lean_dec(v_a_698_);
if (lean_obj_tag(v_fst_702_) == 0)
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_del_object(v___x_700_);
v___x_703_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_704_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v___x_703_, v_a_689_, v_a_690_);
return v___x_704_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; 
v_val_705_ = lean_ctor_get(v_fst_702_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v_fst_702_, 1);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v_val_705_);
v___x_707_ = v___x_700_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_val_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
v_a_710_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_697_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_697_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_692_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_692_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parFirst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_687_ = stack[0].m_obj;
uint8_t v_cancel_688_ = stack[1].m_num;
lean_object* v_a_689_ = stack[2].m_obj;
lean_object* v_a_690_ = stack[3].m_obj;
lean_object* v_res_726_;
v_res_726_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_687_, v_cancel_688_, v_a_689_, v_a_690_);
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg___boxed(lean_object* v_jobs_727_, lean_object* v_cancel_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
uint8_t v_cancel_boxed_732_; lean_object* v_res_733_; 
v_cancel_boxed_732_ = lean_unbox(v_cancel_728_);
v_res_733_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_727_, v_cancel_boxed_732_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
return v_res_733_;
}
}
lean_object* l_Lean_Core_CoreM_parFirst(lean_object* v_00_u03b1_734_, lean_object* v_jobs_735_, uint8_t v_cancel_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_735_, v_cancel_736_, v_a_737_, v_a_738_);
return v___x_740_;
}
}
LEAN_EXPORT void l_Lean_Core_CoreM_parFirst_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_735_ = stack[1].m_obj;
uint8_t v_cancel_736_ = stack[2].m_num;
lean_object* v_a_737_ = stack[3].m_obj;
lean_object* v_a_738_ = stack[4].m_obj;
lean_object* v_res_741_;
v_res_741_ = l_Lean_Core_CoreM_parFirst(lean_box(0), v_jobs_735_, v_cancel_736_, v_a_737_, v_a_738_);
stack->m_obj
 = v_res_741_;
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___boxed(lean_object* v_00_u03b1_742_, lean_object* v_jobs_743_, lean_object* v_cancel_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
uint8_t v_cancel_boxed_748_; lean_object* v_res_749_; 
v_cancel_boxed_748_ = lean_unbox(v_cancel_744_);
v_res_749_ = l_Lean_Core_CoreM_parFirst(v_00_u03b1_742_, v_jobs_743_, v_cancel_boxed_748_, v_a_745_, v_a_746_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_749_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(lean_object* v_00_u03b1_750_, uint8_t v_cancel_751_, lean_object* v_fst_752_, lean_object* v_inst_753_, lean_object* v_R_754_, lean_object* v_a_755_, lean_object* v_b_756_, lean_object* v_c_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_751_, v_fst_752_, v_a_755_, v_b_756_, v___y_758_, v___y_759_);
return v___x_761_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_751_ = stack[1].m_num;
lean_object* v_fst_752_ = stack[2].m_obj;
lean_object* v_a_755_ = stack[5].m_obj;
lean_object* v_b_756_ = stack[6].m_obj;
lean_object* v___y_758_ = stack[8].m_obj;
lean_object* v___y_759_ = stack[9].m_obj;
lean_object* v_res_762_;
v_res_762_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(lean_box(0), v_cancel_751_, v_fst_752_, lean_box(0), lean_box(0), v_a_755_, v_b_756_, lean_box(0), v___y_758_, v___y_759_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_763_, lean_object* v_cancel_764_, lean_object* v_fst_765_, lean_object* v_inst_766_, lean_object* v_R_767_, lean_object* v_a_768_, lean_object* v_b_769_, lean_object* v_c_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
uint8_t v_cancel_boxed_774_; lean_object* v_res_775_; 
v_cancel_boxed_774_ = lean_unbox(v_cancel_764_);
v_res_775_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(v_00_u03b1_763_, v_cancel_boxed_774_, v_fst_765_, v_inst_766_, v_R_767_, v_a_768_, v_b_769_, v_c_770_, v___y_771_, v___y_772_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
return v_res_775_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(lean_object* v_00_u03b1_776_, lean_object* v_msg_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_777_, v___y_778_, v___y_779_);
return v___x_781_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_777_ = stack[1].m_obj;
lean_object* v___y_778_ = stack[2].m_obj;
lean_object* v___y_779_ = stack[3].m_obj;
lean_object* v_res_782_;
v_res_782_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(lean_box(0), v_msg_777_, v___y_778_, v___y_779_);
stack->m_obj
 = v_res_782_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(v_00_u03b1_783_, v_msg_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_788_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
if (lean_obj_tag(v_x_789_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = l_List_reverse___redArg(v_x_790_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
else
{
lean_object* v_head_798_; lean_object* v_tail_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_817_; 
v_head_798_ = lean_ctor_get(v_x_789_, 0);
v_tail_799_ = lean_ctor_get(v_x_789_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_789_);
if (v_isSharedCheck_817_ == 0)
{
v___x_801_ = v_x_789_;
v_isShared_802_ = v_isSharedCheck_817_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_tail_799_);
lean_inc(v_head_798_);
lean_dec(v_x_789_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_817_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_head_798_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v_x_790_);
lean_ctor_set(v___x_801_, 0, v_a_804_);
v___x_806_ = v___x_801_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_804_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_x_790_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v_x_789_ = v_tail_799_;
v_x_790_ = v___x_806_;
goto _start;
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_del_object(v___x_801_);
lean_dec(v_tail_799_);
lean_dec(v_x_790_);
v_a_809_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_803_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_803_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_789_ = stack[0].m_obj;
lean_object* v_x_790_ = stack[1].m_obj;
lean_object* v___y_791_ = stack[2].m_obj;
lean_object* v___y_792_ = stack[3].m_obj;
lean_object* v___y_793_ = stack[4].m_obj;
lean_object* v___y_794_ = stack[5].m_obj;
lean_object* v_res_818_;
v_res_818_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_789_, v_x_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
stack->m_obj
 = v_res_818_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg___boxed(lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_819_, v_x_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_826_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(lean_object* v_as_x27_827_, lean_object* v_b_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
if (lean_obj_tag(v_as_x27_827_) == 0)
{
lean_object* v___x_834_; 
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v_b_828_);
return v___x_834_;
}
else
{
lean_object* v_head_835_; lean_object* v_tail_836_; lean_object* v_a_838_; lean_object* v___y_842_; uint8_t v___y_843_; lean_object* v_a_847_; lean_object* v___x_2356__overap_850_; lean_object* v___x_851_; 
v_head_835_ = lean_ctor_get(v_as_x27_827_, 0);
v_tail_836_ = lean_ctor_get(v_as_x27_827_, 1);
lean_inc(v_head_835_);
v___x_2356__overap_850_ = lean_task_get_own(v_head_835_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
v___x_851_ = lean_apply_5(v___x_2356__overap_850_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, lean_box(0));
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = l_Lean_Meta_saveState___redArg(v___y_830_, v___y_832_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_862_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_a_852_);
lean_ctor_set(v___x_858_, 1, v_a_854_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
lean_ctor_set(v___x_856_, 0, v___x_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
v_a_838_ = v___x_860_;
goto v___jp_837_;
}
}
}
else
{
lean_object* v_a_863_; 
lean_dec(v_a_852_);
v_a_863_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_853_, 1);
v_a_847_ = v_a_863_;
goto v___jp_846_;
}
}
else
{
lean_object* v_a_864_; 
v_a_864_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_864_);
lean_dec_ref_known(v___x_851_, 1);
v_a_847_ = v_a_864_;
goto v___jp_846_;
}
v___jp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_839_, 0, v_a_838_);
lean_ctor_set(v___x_839_, 1, v_b_828_);
v_as_x27_827_ = v_tail_836_;
v_b_828_ = v___x_839_;
goto _start;
}
v___jp_841_:
{
if (v___y_843_ == 0)
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___y_842_);
v_a_838_ = v___x_844_;
goto v___jp_837_;
}
else
{
lean_object* v___x_845_; 
lean_dec(v_b_828_);
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v___y_842_);
return v___x_845_;
}
}
v___jp_846_:
{
uint8_t v___x_848_; 
v___x_848_ = l_Lean_Exception_isInterrupt(v_a_847_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; 
lean_inc_ref(v_a_847_);
v___x_849_ = l_Lean_Exception_isRuntime(v_a_847_);
v___y_842_ = v_a_847_;
v___y_843_ = v___x_849_;
goto v___jp_841_;
}
else
{
v___y_842_ = v_a_847_;
v___y_843_ = v___x_848_;
goto v___jp_841_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_827_ = stack[0].m_obj;
lean_object* v_b_828_ = stack[1].m_obj;
lean_object* v___y_829_ = stack[2].m_obj;
lean_object* v___y_830_ = stack[3].m_obj;
lean_object* v___y_831_ = stack[4].m_obj;
lean_object* v___y_832_ = stack[5].m_obj;
lean_object* v_res_865_;
v_res_865_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_827_, v_b_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
stack->m_obj
 = v_res_865_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg___boxed(lean_object* v_as_x27_866_, lean_object* v_b_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_866_, v_b_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v_as_x27_866_);
return v_res_873_;
}
}
lean_object* l_Lean_Meta_MetaM_par___redArg(lean_object* v_jobs_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_st_ref_get(v_a_876_);
v___x_881_ = lean_box(0);
v___x_882_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_874_, v___x_881_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_a_883_, v___x_881_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_894_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = lean_st_ref_swap(v_a_876_, v___x_880_);
lean_dec(v___x_889_);
v___x_890_ = l_List_reverse___redArg(v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_dec(v___x_880_);
return v___x_884_;
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec(v___x_880_);
v_a_895_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_882_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_882_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_par___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_874_ = stack[0].m_obj;
lean_object* v_a_875_ = stack[1].m_obj;
lean_object* v_a_876_ = stack[2].m_obj;
lean_object* v_a_877_ = stack[3].m_obj;
lean_object* v_a_878_ = stack[4].m_obj;
lean_object* v_res_903_;
v_res_903_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg___boxed(lean_object* v_jobs_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_910_;
}
}
lean_object* l_Lean_Meta_MetaM_par(lean_object* v_00_u03b1_911_, lean_object* v_jobs_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_918_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_par_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_912_ = stack[1].m_obj;
lean_object* v_a_913_ = stack[2].m_obj;
lean_object* v_a_914_ = stack[3].m_obj;
lean_object* v_a_915_ = stack[4].m_obj;
lean_object* v_a_916_ = stack[5].m_obj;
lean_object* v_res_919_;
v_res_919_ = l_Lean_Meta_MetaM_par(lean_box(0), v_jobs_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___boxed(lean_object* v_00_u03b1_920_, lean_object* v_jobs_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_MetaM_par(v_00_u03b1_920_, v_jobs_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_927_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(lean_object* v_00_u03b1_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_929_, v_x_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
return v___x_936_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_929_ = stack[1].m_obj;
lean_object* v_x_930_ = stack[2].m_obj;
lean_object* v___y_931_ = stack[3].m_obj;
lean_object* v___y_932_ = stack[4].m_obj;
lean_object* v___y_933_ = stack[5].m_obj;
lean_object* v___y_934_ = stack[6].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(lean_box(0), v_x_929_, v_x_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___boxed(lean_object* v_00_u03b1_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(v_00_u03b1_938_, v_x_939_, v_x_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
return v_res_946_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(lean_object* v_00_u03b1_947_, lean_object* v_as_948_, lean_object* v_as_x27_949_, lean_object* v_b_950_, lean_object* v_a_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_949_, v_b_950_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
return v___x_957_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_948_ = stack[1].m_obj;
lean_object* v_as_x27_949_ = stack[2].m_obj;
lean_object* v_b_950_ = stack[3].m_obj;
lean_object* v___y_952_ = stack[5].m_obj;
lean_object* v___y_953_ = stack[6].m_obj;
lean_object* v___y_954_ = stack[7].m_obj;
lean_object* v___y_955_ = stack[8].m_obj;
lean_object* v_res_958_;
v_res_958_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(lean_box(0), v_as_948_, v_as_x27_949_, v_b_950_, lean_box(0), v___y_952_, v___y_953_, v___y_954_, v___y_955_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___boxed(lean_object* v_00_u03b1_959_, lean_object* v_as_960_, lean_object* v_as_x27_961_, lean_object* v_b_962_, lean_object* v_a_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(v_00_u03b1_959_, v_as_960_, v_as_x27_961_, v_b_962_, v_a_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v_as_x27_961_);
lean_dec(v_as_960_);
return v_res_969_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(lean_object* v_as_x27_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
if (lean_obj_tag(v_as_x27_970_) == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_b_971_);
return v___x_977_;
}
else
{
lean_object* v_head_978_; lean_object* v_tail_979_; lean_object* v___x_2059__overap_980_; lean_object* v___x_981_; 
v_head_978_ = lean_ctor_get(v_as_x27_970_, 0);
v_tail_979_ = lean_ctor_get(v_as_x27_970_, 1);
lean_inc(v_head_978_);
v___x_2059__overap_980_ = lean_task_get_own(v_head_978_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
v___x_981_ = lean_apply_5(v___x_2059__overap_980_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, lean_box(0));
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v_a_982_);
v___x_984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_b_971_);
v_as_x27_970_ = v_tail_979_;
v_b_971_ = v___x_984_;
goto _start;
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1000_; 
v_a_986_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_988_ = v___x_981_;
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_981_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___y_991_; uint8_t v___x_998_; 
v___x_998_ = l_Lean_Exception_isInterrupt(v_a_986_);
if (v___x_998_ == 0)
{
uint8_t v___x_999_; 
lean_inc(v_a_986_);
v___x_999_ = l_Lean_Exception_isRuntime(v_a_986_);
v___y_991_ = v___x_999_;
goto v___jp_990_;
}
else
{
v___y_991_ = v___x_998_;
goto v___jp_990_;
}
v___jp_990_:
{
if (v___y_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_988_);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_a_986_);
v___x_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v_b_971_);
v_as_x27_970_ = v_tail_979_;
v_b_971_ = v___x_993_;
goto _start;
}
else
{
lean_object* v___x_996_; 
lean_dec(v_b_971_);
if (v_isShared_989_ == 0)
{
v___x_996_ = v___x_988_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_986_);
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
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_970_ = stack[0].m_obj;
lean_object* v_b_971_ = stack[1].m_obj;
lean_object* v___y_972_ = stack[2].m_obj;
lean_object* v___y_973_ = stack[3].m_obj;
lean_object* v___y_974_ = stack[4].m_obj;
lean_object* v___y_975_ = stack[5].m_obj;
lean_object* v_res_1001_;
v_res_1001_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_970_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
stack->m_obj
 = v_res_1001_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_1002_, lean_object* v_b_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_1002_, v_b_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v_as_x27_1002_);
return v_res_1009_;
}
}
lean_object* l_Lean_Meta_MetaM_par_x27___redArg(lean_object* v_jobs_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1016_ = lean_st_ref_get(v_a_1012_);
v___x_1017_ = lean_box(0);
v___x_1018_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_1010_, v___x_1017_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_a_1019_, v___x_1017_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1019_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1030_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1030_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1025_ = lean_st_ref_swap(v_a_1012_, v___x_1016_);
lean_dec(v___x_1025_);
v___x_1026_ = l_List_reverse___redArg(v_a_1021_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1026_);
v___x_1028_ = v___x_1023_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
else
{
lean_dec(v___x_1016_);
return v___x_1020_;
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_dec(v___x_1016_);
v_a_1031_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1018_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1018_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_par_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1010_ = stack[0].m_obj;
lean_object* v_a_1011_ = stack[1].m_obj;
lean_object* v_a_1012_ = stack[2].m_obj;
lean_object* v_a_1013_ = stack[3].m_obj;
lean_object* v_a_1014_ = stack[4].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg___boxed(lean_object* v_jobs_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
return v_res_1046_;
}
}
lean_object* l_Lean_Meta_MetaM_par_x27(lean_object* v_00_u03b1_1047_, lean_object* v_jobs_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_par_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1048_ = stack[1].m_obj;
lean_object* v_a_1049_ = stack[2].m_obj;
lean_object* v_a_1050_ = stack[3].m_obj;
lean_object* v_a_1051_ = stack[4].m_obj;
lean_object* v_a_1052_ = stack[5].m_obj;
lean_object* v_res_1055_;
v_res_1055_ = l_Lean_Meta_MetaM_par_x27(lean_box(0), v_jobs_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
stack->m_obj
 = v_res_1055_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___boxed(lean_object* v_00_u03b1_1056_, lean_object* v_jobs_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_MetaM_par_x27(v_00_u03b1_1056_, v_jobs_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1063_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(lean_object* v_00_u03b1_1064_, lean_object* v_as_1065_, lean_object* v_as_x27_1066_, lean_object* v_b_1067_, lean_object* v_a_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_1066_, v_b_1067_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1065_ = stack[1].m_obj;
lean_object* v_as_x27_1066_ = stack[2].m_obj;
lean_object* v_b_1067_ = stack[3].m_obj;
lean_object* v___y_1069_ = stack[5].m_obj;
lean_object* v___y_1070_ = stack[6].m_obj;
lean_object* v___y_1071_ = stack[7].m_obj;
lean_object* v___y_1072_ = stack[8].m_obj;
lean_object* v_res_1075_;
v_res_1075_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(lean_box(0), v_as_1065_, v_as_x27_1066_, v_b_1067_, lean_box(0), v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
stack->m_obj
 = v_res_1075_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_as_1077_, lean_object* v_as_x27_1078_, lean_object* v_b_1079_, lean_object* v_a_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(v_00_u03b1_1076_, v_as_1077_, v_as_x27_1078_, v_b_1079_, v_a_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v_as_x27_1078_);
lean_dec(v_as_1077_);
return v_res_1086_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1087_, lean_object* v_x_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
if (lean_obj_tag(v_x_1087_) == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = l_List_reverse___redArg(v_x_1088_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
else
{
lean_object* v_head_1096_; lean_object* v_tail_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1115_; 
v_head_1096_ = lean_ctor_get(v_x_1087_, 0);
v_tail_1097_ = lean_ctor_get(v_x_1087_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1087_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1099_ = v_x_1087_;
v_isShared_1100_ = v_isSharedCheck_1115_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_tail_1097_);
lean_inc(v_head_1096_);
lean_dec(v_x_1087_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1115_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Meta_MetaM_asTask___redArg(v_head_1096_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 1, v_x_1088_);
lean_ctor_set(v___x_1099_, 0, v_a_1102_);
v___x_1104_ = v___x_1099_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1102_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_x_1088_);
v___x_1104_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v_x_1087_ = v_tail_1097_;
v_x_1088_ = v___x_1104_;
goto _start;
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1099_);
lean_dec(v_tail_1097_);
lean_dec(v_x_1088_);
v_a_1107_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1101_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1101_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1087_ = stack[0].m_obj;
lean_object* v_x_1088_ = stack[1].m_obj;
lean_object* v___y_1089_ = stack[2].m_obj;
lean_object* v___y_1090_ = stack[3].m_obj;
lean_object* v___y_1091_ = stack[4].m_obj;
lean_object* v___y_1092_ = stack[5].m_obj;
lean_object* v_res_1116_;
v_res_1116_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1087_, v_x_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
stack->m_obj
 = v_res_1116_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1117_, v_x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg(lean_object* v_jobs_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1125_, v___x_1131_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1151_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1151_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1151_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1150_; 
v___x_1137_ = l_List_unzipTR___redArg(v_a_1133_);
v_fst_1138_ = lean_ctor_get(v___x_1137_, 0);
v_snd_1139_ = lean_ctor_get(v___x_1137_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1141_ = v___x_1137_;
v_isShared_1142_ = v_isSharedCheck_1150_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_snd_1139_);
lean_inc(v_fst_1138_);
lean_dec(v___x_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1150_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1143_, 0, v_fst_1138_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_snd_1139_);
v___x_1145_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1147_; 
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1145_);
v___x_1147_ = v___x_1135_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1132_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1132_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parIterWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1125_ = stack[0].m_obj;
lean_object* v_a_1126_ = stack[1].m_obj;
lean_object* v_a_1127_ = stack[2].m_obj;
lean_object* v_a_1128_ = stack[3].m_obj;
lean_object* v_a_1129_ = stack[4].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
return v_res_1167_;
}
}
lean_object* l_Lean_Meta_MetaM_parIterWithCancel(lean_object* v_00_u03b1_1168_, lean_object* v_jobs_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parIterWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1169_ = stack[1].m_obj;
lean_object* v_a_1170_ = stack[2].m_obj;
lean_object* v_a_1171_ = stack[3].m_obj;
lean_object* v_a_1172_ = stack[4].m_obj;
lean_object* v_a_1173_ = stack[5].m_obj;
lean_object* v_res_1176_;
v_res_1176_ = l_Lean_Meta_MetaM_parIterWithCancel(lean_box(0), v_jobs_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
stack->m_obj
 = v_res_1176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_jobs_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_MetaM_parIterWithCancel(v_00_u03b1_1177_, v_jobs_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1184_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1185_, lean_object* v_x_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1186_ = stack[1].m_obj;
lean_object* v_x_1187_ = stack[2].m_obj;
lean_object* v___y_1188_ = stack[3].m_obj;
lean_object* v___y_1189_ = stack[4].m_obj;
lean_object* v___y_1190_ = stack[5].m_obj;
lean_object* v___y_1191_ = stack[6].m_obj;
lean_object* v_res_1194_;
v_res_1194_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(lean_box(0), v_x_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
stack->m_obj
 = v_res_1194_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1195_, lean_object* v_x_1196_, lean_object* v_x_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(v_00_u03b1_1195_, v_x_1196_, v_x_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
return v_res_1203_;
}
}
lean_object* l_Lean_Meta_MetaM_parIter___redArg(lean_object* v_jobs_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_snd_1215_; lean_object* v___x_1217_; 
v_snd_1215_ = lean_ctor_get(v_a_1211_, 1);
lean_inc(v_snd_1215_);
lean_dec(v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_snd_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_snd_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1210_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1210_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parIter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1204_ = stack[0].m_obj;
lean_object* v_a_1205_ = stack[1].m_obj;
lean_object* v_a_1206_ = stack[2].m_obj;
lean_object* v_a_1207_ = stack[3].m_obj;
lean_object* v_a_1208_ = stack[4].m_obj;
lean_object* v_res_1228_;
v_res_1228_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg___boxed(lean_object* v_jobs_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1235_;
}
}
lean_object* l_Lean_Meta_MetaM_parIter(lean_object* v_00_u03b1_1236_, lean_object* v_jobs_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parIter_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1237_ = stack[1].m_obj;
lean_object* v_a_1238_ = stack[2].m_obj;
lean_object* v_a_1239_ = stack[3].m_obj;
lean_object* v_a_1240_ = stack[4].m_obj;
lean_object* v_a_1241_ = stack[5].m_obj;
lean_object* v_res_1244_;
v_res_1244_ = l_Lean_Meta_MetaM_parIter(lean_box(0), v_jobs_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_);
stack->m_obj
 = v_res_1244_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___boxed(lean_object* v_00_u03b1_1245_, lean_object* v_jobs_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Meta_MetaM_parIter(v_00_u03b1_1245_, v_jobs_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
return v_res_1252_;
}
}
lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_box(0);
v___x_1260_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1253_, v___x_1259_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1279_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1279_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1279_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v_fst_1266_; lean_object* v_snd_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1278_; 
v___x_1265_ = l_List_unzipTR___redArg(v_a_1261_);
v_fst_1266_ = lean_ctor_get(v___x_1265_, 0);
v_snd_1267_ = lean_ctor_get(v___x_1265_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1269_ = v___x_1265_;
v_isShared_1270_ = v_isSharedCheck_1278_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_snd_1267_);
lean_inc(v_fst_1266_);
lean_dec(v___x_1265_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1278_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1271_, 0, v_fst_1266_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_snd_1267_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1273_);
v___x_1275_ = v___x_1263_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1260_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1260_);
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
LEAN_EXPORT void l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1253_ = stack[0].m_obj;
lean_object* v_a_1254_ = stack[1].m_obj;
lean_object* v_a_1255_ = stack[2].m_obj;
lean_object* v_a_1256_ = stack[3].m_obj;
lean_object* v_a_1257_ = stack[4].m_obj;
lean_object* v_res_1288_;
v_res_1288_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
stack->m_obj
 = v_res_1288_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
return v_res_1295_;
}
}
lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1296_, lean_object* v_jobs_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parIterGreedyWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1297_ = stack[1].m_obj;
lean_object* v_a_1298_ = stack[2].m_obj;
lean_object* v_a_1299_ = stack[3].m_obj;
lean_object* v_a_1300_ = stack[4].m_obj;
lean_object* v_a_1301_ = stack[5].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel(lean_box(0), v_jobs_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_jobs_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel(v_00_u03b1_1305_, v_jobs_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
return v_res_1312_;
}
}
lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg(lean_object* v_jobs_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v_snd_1324_; lean_object* v___x_1326_; 
v_snd_1324_ = lean_ctor_get(v_a_1320_, 1);
lean_inc(v_snd_1324_);
lean_dec(v_a_1320_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_snd_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_snd_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1319_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1319_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parIterGreedy___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1313_ = stack[0].m_obj;
lean_object* v_a_1314_ = stack[1].m_obj;
lean_object* v_a_1315_ = stack[2].m_obj;
lean_object* v_a_1316_ = stack[3].m_obj;
lean_object* v_a_1317_ = stack[4].m_obj;
lean_object* v_res_1337_;
v_res_1337_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
stack->m_obj
 = v_res_1337_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec(v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
return v_res_1344_;
}
}
lean_object* l_Lean_Meta_MetaM_parIterGreedy(lean_object* v_00_u03b1_1345_, lean_object* v_jobs_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parIterGreedy_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1346_ = stack[1].m_obj;
lean_object* v_a_1347_ = stack[2].m_obj;
lean_object* v_a_1348_ = stack[3].m_obj;
lean_object* v_a_1349_ = stack[4].m_obj;
lean_object* v_a_1350_ = stack[5].m_obj;
lean_object* v_res_1353_;
v_res_1353_ = l_Lean_Meta_MetaM_parIterGreedy(lean_box(0), v_jobs_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
stack->m_obj
 = v_res_1353_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___boxed(lean_object* v_00_u03b1_1354_, lean_object* v_jobs_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_MetaM_parIterGreedy(v_00_u03b1_1354_, v_jobs_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
return v_res_1361_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_1362_, lean_object* v___x_1363_, lean_object* v_____r_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_a_1362_);
v___x_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___x_1363_);
v___x_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1362_ = stack[0].m_obj;
lean_object* v___x_1363_ = stack[1].m_obj;
lean_object* v_____r_1364_ = stack[2].m_obj;
lean_object* v___y_1365_ = stack[3].m_obj;
lean_object* v___y_1366_ = stack[4].m_obj;
lean_object* v___y_1367_ = stack[5].m_obj;
lean_object* v___y_1368_ = stack[6].m_obj;
lean_object* v_res_1374_;
v_res_1374_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1362_, v___x_1363_, v_____r_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
stack->m_obj
 = v_res_1374_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_1375_, lean_object* v___x_1376_, lean_object* v_____r_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1375_, v___x_1376_, v_____r_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1383_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(uint8_t v_cancel_1384_, lean_object* v_fst_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
if (lean_obj_tag(v_a_1386_) == 0)
{
lean_object* v___x_1393_; 
lean_dec_ref(v_fst_1385_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_b_1387_);
return v___x_1393_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___y_1400_; lean_object* v___x_1420_; 
lean_dec_ref(v_b_1387_);
v___x_1394_ = lean_box(0);
v___x_1395_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1396_ = l_IO_waitAny_x27___redArg(v_a_1386_);
v_fst_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_fst_1397_);
v_snd_1398_ = lean_ctor_get(v___x_1396_, 1);
lean_inc(v_snd_1398_);
lean_dec_ref(v___x_1396_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v___y_1389_);
lean_inc_ref(v___y_1388_);
v___x_1420_ = lean_apply_5(v_fst_1397_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, lean_box(0));
if (lean_obj_tag(v___x_1420_) == 0)
{
if (v_cancel_1384_ == 0)
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref_known(v___x_1420_, 1);
v___x_1422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1421_, v___x_1394_, v___x_1394_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
v___y_1400_ = v___x_1422_;
goto v___jp_1399_;
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_a_1423_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1420_, 1);
lean_inc_ref(v_fst_1385_);
v___x_1424_ = lean_apply_1(v_fst_1385_, lean_box(0));
v___x_1425_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1423_, v___x_1394_, v___x_1424_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
v___y_1400_ = v___x_1425_;
goto v___jp_1399_;
}
}
else
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1438_; 
v_a_1426_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1428_ = v___x_1420_;
v_isShared_1429_ = v_isSharedCheck_1438_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1420_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1438_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
uint8_t v___y_1431_; uint8_t v___x_1436_; 
v___x_1436_ = l_Lean_Exception_isInterrupt(v_a_1426_);
if (v___x_1436_ == 0)
{
uint8_t v___x_1437_; 
lean_inc(v_a_1426_);
v___x_1437_ = l_Lean_Exception_isRuntime(v_a_1426_);
v___y_1431_ = v___x_1437_;
goto v___jp_1430_;
}
else
{
v___y_1431_ = v___x_1436_;
goto v___jp_1430_;
}
v___jp_1430_:
{
if (v___y_1431_ == 0)
{
lean_del_object(v___x_1428_);
lean_dec(v_a_1426_);
v_a_1386_ = v_snd_1398_;
v_b_1387_ = v___x_1395_;
goto _start;
}
else
{
lean_object* v___x_1434_; 
lean_dec(v_snd_1398_);
lean_dec_ref(v_fst_1385_);
if (v_isShared_1429_ == 0)
{
v___x_1434_ = v___x_1428_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1426_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
v___jp_1399_:
{
if (lean_obj_tag(v___y_1400_) == 0)
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1411_; 
v_a_1401_ = lean_ctor_get(v___y_1400_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___y_1400_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1403_ = v___y_1400_;
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___y_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1411_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
if (lean_obj_tag(v_a_1401_) == 0)
{
lean_object* v_a_1405_; lean_object* v___x_1407_; 
lean_dec(v_snd_1398_);
lean_dec_ref(v_fst_1385_);
v_a_1405_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v_a_1401_, 1);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_a_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v_a_1409_; 
lean_del_object(v___x_1403_);
v_a_1409_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v_a_1401_, 1);
v_a_1386_ = v_snd_1398_;
v_b_1387_ = v_a_1409_;
goto _start;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v_snd_1398_);
lean_dec_ref(v_fst_1385_);
v_a_1412_ = lean_ctor_get(v___y_1400_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___y_1400_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___y_1400_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___y_1400_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_1384_ = stack[0].m_num;
lean_object* v_fst_1385_ = stack[1].m_obj;
lean_object* v_a_1386_ = stack[2].m_obj;
lean_object* v_b_1387_ = stack[3].m_obj;
lean_object* v___y_1388_ = stack[4].m_obj;
lean_object* v___y_1389_ = stack[5].m_obj;
lean_object* v___y_1390_ = stack[6].m_obj;
lean_object* v___y_1391_ = stack[7].m_obj;
lean_object* v_res_1439_;
v_res_1439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1384_, v_fst_1385_, v_a_1386_, v_b_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
stack->m_obj
 = v_res_1439_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_1440_, lean_object* v_fst_1441_, lean_object* v_a_1442_, lean_object* v_b_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
uint8_t v_cancel_boxed_1449_; lean_object* v_res_1450_; 
v_cancel_boxed_1449_ = lean_unbox(v_cancel_1440_);
v_res_1450_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_boxed_1449_, v_fst_1441_, v_a_1442_, v_b_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
return v_res_1450_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(lean_object* v_msgData_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v_env_1458_; uint8_t v___x_1459_; lean_object* v_env_1460_; lean_object* v___x_1461_; lean_object* v_toCold_1462_; lean_object* v_mctx_1463_; lean_object* v_lctx_1464_; lean_object* v_options_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1457_ = lean_st_ref_get(v___y_1455_);
v_env_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc_ref(v_env_1458_);
lean_dec(v___x_1457_);
v___x_1459_ = 0;
v_env_1460_ = l_Lean_Environment_setRecordingDeps(v_env_1458_, v___x_1459_);
v___x_1461_ = lean_st_ref_get(v___y_1453_);
v_toCold_1462_ = lean_ctor_get(v___y_1454_, 0);
v_mctx_1463_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_mctx_1463_);
lean_dec(v___x_1461_);
v_lctx_1464_ = lean_ctor_get(v___y_1452_, 2);
v_options_1465_ = lean_ctor_get(v_toCold_1462_, 2);
lean_inc_ref(v_options_1465_);
lean_inc_ref(v_lctx_1464_);
v___x_1466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1466_, 0, v_env_1460_);
lean_ctor_set(v___x_1466_, 1, v_mctx_1463_);
lean_ctor_set(v___x_1466_, 2, v_lctx_1464_);
lean_ctor_set(v___x_1466_, 3, v_options_1465_);
v___x_1467_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
lean_ctor_set(v___x_1467_, 1, v_msgData_1451_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1451_ = stack[0].m_obj;
lean_object* v___y_1452_ = stack[1].m_obj;
lean_object* v___y_1453_ = stack[2].m_obj;
lean_object* v___y_1454_ = stack[3].m_obj;
lean_object* v___y_1455_ = stack[4].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msgData_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msgData_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
return v_res_1476_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(lean_object* v_msg_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_ref_1483_; lean_object* v___x_1484_; lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_ref_1483_ = lean_ctor_get(v___y_1480_, 2);
v___x_1484_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
lean_inc(v_ref_1483_);
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_ref_1483_);
lean_ctor_set(v___x_1489_, 1, v_a_1485_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 1);
lean_ctor_set(v___x_1487_, 0, v___x_1489_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1477_ = stack[0].m_obj;
lean_object* v___y_1478_ = stack[1].m_obj;
lean_object* v___y_1479_ = stack[2].m_obj;
lean_object* v___y_1480_ = stack[3].m_obj;
lean_object* v___y_1481_ = stack[4].m_obj;
lean_object* v_res_1494_;
v_res_1494_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
stack->m_obj
 = v_res_1494_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
return v_res_1501_;
}
}
lean_object* l_Lean_Meta_MetaM_parFirst___redArg(lean_object* v_jobs_1502_, uint8_t v_cancel_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1502_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v_fst_1511_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_fst_1511_);
v_snd_1512_ = lean_ctor_get(v_a_1510_, 1);
lean_inc(v_snd_1512_);
lean_dec(v_a_1510_);
v___x_1513_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1514_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1503_, v_fst_1511_, v_snd_1512_, v___x_1513_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1526_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1526_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_fst_1519_; 
v_fst_1519_ = lean_ctor_get(v_a_1515_, 0);
lean_inc(v_fst_1519_);
lean_dec(v_a_1515_);
if (lean_obj_tag(v_fst_1519_) == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_del_object(v___x_1517_);
v___x_1520_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_1521_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v___x_1520_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
return v___x_1521_;
}
else
{
lean_object* v_val_1522_; lean_object* v___x_1524_; 
v_val_1522_ = lean_ctor_get(v_fst_1519_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v_fst_1519_, 1);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v_val_1522_);
v___x_1524_ = v___x_1517_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_val_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
v_a_1527_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1514_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1514_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v___x_1509_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1509_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parFirst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1502_ = stack[0].m_obj;
uint8_t v_cancel_1503_ = stack[1].m_num;
lean_object* v_a_1504_ = stack[2].m_obj;
lean_object* v_a_1505_ = stack[3].m_obj;
lean_object* v_a_1506_ = stack[4].m_obj;
lean_object* v_a_1507_ = stack[5].m_obj;
lean_object* v_res_1543_;
v_res_1543_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1502_, v_cancel_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
stack->m_obj
 = v_res_1543_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg___boxed(lean_object* v_jobs_1544_, lean_object* v_cancel_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_){
_start:
{
uint8_t v_cancel_boxed_1551_; lean_object* v_res_1552_; 
v_cancel_boxed_1551_ = lean_unbox(v_cancel_1545_);
v_res_1552_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1544_, v_cancel_boxed_1551_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
lean_dec(v_a_1549_);
lean_dec_ref(v_a_1548_);
lean_dec(v_a_1547_);
lean_dec_ref(v_a_1546_);
return v_res_1552_;
}
}
lean_object* l_Lean_Meta_MetaM_parFirst(lean_object* v_00_u03b1_1553_, lean_object* v_jobs_1554_, uint8_t v_cancel_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1554_, v_cancel_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
return v___x_1561_;
}
}
LEAN_EXPORT void l_Lean_Meta_MetaM_parFirst_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1554_ = stack[1].m_obj;
uint8_t v_cancel_1555_ = stack[2].m_num;
lean_object* v_a_1556_ = stack[3].m_obj;
lean_object* v_a_1557_ = stack[4].m_obj;
lean_object* v_a_1558_ = stack[5].m_obj;
lean_object* v_a_1559_ = stack[6].m_obj;
lean_object* v_res_1562_;
v_res_1562_ = l_Lean_Meta_MetaM_parFirst(lean_box(0), v_jobs_1554_, v_cancel_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
stack->m_obj
 = v_res_1562_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___boxed(lean_object* v_00_u03b1_1563_, lean_object* v_jobs_1564_, lean_object* v_cancel_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
uint8_t v_cancel_boxed_1571_; lean_object* v_res_1572_; 
v_cancel_boxed_1571_ = lean_unbox(v_cancel_1565_);
v_res_1572_ = l_Lean_Meta_MetaM_parFirst(v_00_u03b1_1563_, v_jobs_1564_, v_cancel_boxed_1571_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
return v_res_1572_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(lean_object* v_00_u03b1_1573_, uint8_t v_cancel_1574_, lean_object* v_fst_1575_, lean_object* v_inst_1576_, lean_object* v_R_1577_, lean_object* v_a_1578_, lean_object* v_b_1579_, lean_object* v_c_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1574_, v_fst_1575_, v_a_1578_, v_b_1579_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
return v___x_1586_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_1574_ = stack[1].m_num;
lean_object* v_fst_1575_ = stack[2].m_obj;
lean_object* v_a_1578_ = stack[5].m_obj;
lean_object* v_b_1579_ = stack[6].m_obj;
lean_object* v___y_1581_ = stack[8].m_obj;
lean_object* v___y_1582_ = stack[9].m_obj;
lean_object* v___y_1583_ = stack[10].m_obj;
lean_object* v___y_1584_ = stack[11].m_obj;
lean_object* v_res_1587_;
v_res_1587_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(lean_box(0), v_cancel_1574_, v_fst_1575_, lean_box(0), lean_box(0), v_a_1578_, v_b_1579_, lean_box(0), v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
stack->m_obj
 = v_res_1587_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_cancel_1589_, lean_object* v_fst_1590_, lean_object* v_inst_1591_, lean_object* v_R_1592_, lean_object* v_a_1593_, lean_object* v_b_1594_, lean_object* v_c_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_cancel_boxed_1601_; lean_object* v_res_1602_; 
v_cancel_boxed_1601_ = lean_unbox(v_cancel_1589_);
v_res_1602_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(v_00_u03b1_1588_, v_cancel_boxed_1601_, v_fst_1590_, v_inst_1591_, v_R_1592_, v_a_1593_, v_b_1594_, v_c_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1602_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(lean_object* v_00_u03b1_1603_, lean_object* v_msg_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1604_ = stack[1].m_obj;
lean_object* v___y_1605_ = stack[2].m_obj;
lean_object* v___y_1606_ = stack[3].m_obj;
lean_object* v___y_1607_ = stack[4].m_obj;
lean_object* v___y_1608_ = stack[5].m_obj;
lean_object* v_res_1611_;
v_res_1611_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(lean_box(0), v_msg_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
stack->m_obj
 = v_res_1611_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_msg_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(v_00_u03b1_1612_, v_msg_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
return v_res_1619_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
if (lean_obj_tag(v_x_1620_) == 0)
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = l_List_reverse___redArg(v_x_1621_);
v___x_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
return v___x_1630_;
}
else
{
lean_object* v_head_1631_; lean_object* v_tail_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1650_; 
v_head_1631_ = lean_ctor_get(v_x_1620_, 0);
v_tail_1632_ = lean_ctor_get(v_x_1620_, 1);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1620_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1634_ = v_x_1620_;
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_tail_1632_);
lean_inc(v_head_1631_);
lean_dec(v_x_1620_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1650_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_head_1631_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 1, v_x_1621_);
lean_ctor_set(v___x_1634_, 0, v_a_1637_);
v___x_1639_ = v___x_1634_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1637_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_x_1621_);
v___x_1639_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
v_x_1620_ = v_tail_1632_;
v_x_1621_ = v___x_1639_;
goto _start;
}
}
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_del_object(v___x_1634_);
lean_dec(v_tail_1632_);
lean_dec(v_x_1621_);
v_a_1642_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1636_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1636_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1620_ = stack[0].m_obj;
lean_object* v_x_1621_ = stack[1].m_obj;
lean_object* v___y_1622_ = stack[2].m_obj;
lean_object* v___y_1623_ = stack[3].m_obj;
lean_object* v___y_1624_ = stack[4].m_obj;
lean_object* v___y_1625_ = stack[5].m_obj;
lean_object* v___y_1626_ = stack[6].m_obj;
lean_object* v___y_1627_ = stack[7].m_obj;
lean_object* v_res_1651_;
v_res_1651_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1620_, v_x_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
stack->m_obj
 = v_res_1651_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1652_, lean_object* v_x_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1652_, v_x_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
return v_res_1661_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(lean_object* v_jobs_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_box(0);
v___x_1671_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1662_, v___x_1670_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1690_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1690_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1690_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v_fst_1677_; lean_object* v_snd_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1689_; 
v___x_1676_ = l_List_unzipTR___redArg(v_a_1672_);
v_fst_1677_ = lean_ctor_get(v___x_1676_, 0);
v_snd_1678_ = lean_ctor_get(v___x_1676_, 1);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1680_ = v___x_1676_;
v_isShared_1681_ = v_isSharedCheck_1689_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_snd_1678_);
lean_inc(v_fst_1677_);
lean_dec(v___x_1676_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1689_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1682_, 0, v_fst_1677_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_snd_1678_);
v___x_1684_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1686_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1684_);
v___x_1686_ = v___x_1674_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_a_1691_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1671_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1671_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1662_ = stack[0].m_obj;
lean_object* v_a_1663_ = stack[1].m_obj;
lean_object* v_a_1664_ = stack[2].m_obj;
lean_object* v_a_1665_ = stack[3].m_obj;
lean_object* v_a_1666_ = stack[4].m_obj;
lean_object* v_a_1667_ = stack[5].m_obj;
lean_object* v_a_1668_ = stack[6].m_obj;
lean_object* v_res_1699_;
v_res_1699_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
stack->m_obj
 = v_res_1699_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
lean_dec(v_a_1706_);
lean_dec_ref(v_a_1705_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1708_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel(lean_object* v_00_u03b1_1709_, lean_object* v_jobs_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIterWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1710_ = stack[1].m_obj;
lean_object* v_a_1711_ = stack[2].m_obj;
lean_object* v_a_1712_ = stack[3].m_obj;
lean_object* v_a_1713_ = stack[4].m_obj;
lean_object* v_a_1714_ = stack[5].m_obj;
lean_object* v_a_1715_ = stack[6].m_obj;
lean_object* v_a_1716_ = stack[7].m_obj;
lean_object* v_res_1719_;
v_res_1719_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel(lean_box(0), v_jobs_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
stack->m_obj
 = v_res_1719_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_jobs_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel(v_00_u03b1_1720_, v_jobs_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1729_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1731_, v_x_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1731_ = stack[1].m_obj;
lean_object* v_x_1732_ = stack[2].m_obj;
lean_object* v___y_1733_ = stack[3].m_obj;
lean_object* v___y_1734_ = stack[4].m_obj;
lean_object* v___y_1735_ = stack[5].m_obj;
lean_object* v___y_1736_ = stack[6].m_obj;
lean_object* v___y_1737_ = stack[7].m_obj;
lean_object* v___y_1738_ = stack[8].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(lean_box(0), v_x_1731_, v_x_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1742_, lean_object* v_x_1743_, lean_object* v_x_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(v_00_u03b1_1742_, v_x_1743_, v_x_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
return v_res_1752_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg(lean_object* v_jobs_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_snd_1766_; lean_object* v___x_1768_; 
v_snd_1766_ = lean_ctor_get(v_a_1762_, 1);
lean_inc(v_snd_1766_);
lean_dec(v_a_1762_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v_snd_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_snd_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
v_a_1771_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1761_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1761_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1753_ = stack[0].m_obj;
lean_object* v_a_1754_ = stack[1].m_obj;
lean_object* v_a_1755_ = stack[2].m_obj;
lean_object* v_a_1756_ = stack[3].m_obj;
lean_object* v_a_1757_ = stack[4].m_obj;
lean_object* v_a_1758_ = stack[5].m_obj;
lean_object* v_a_1759_ = stack[6].m_obj;
lean_object* v_res_1779_;
v_res_1779_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
stack->m_obj
 = v_res_1779_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg___boxed(lean_object* v_jobs_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1788_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIter(lean_object* v_00_u03b1_1789_, lean_object* v_jobs_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
return v___x_1798_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIter_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1790_ = stack[1].m_obj;
lean_object* v_a_1791_ = stack[2].m_obj;
lean_object* v_a_1792_ = stack[3].m_obj;
lean_object* v_a_1793_ = stack[4].m_obj;
lean_object* v_a_1794_ = stack[5].m_obj;
lean_object* v_a_1795_ = stack[6].m_obj;
lean_object* v_a_1796_ = stack[7].m_obj;
lean_object* v_res_1799_;
v_res_1799_ = l_Lean_Elab_Term_TermElabM_parIter(lean_box(0), v_jobs_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
stack->m_obj
 = v_res_1799_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___boxed(lean_object* v_00_u03b1_1800_, lean_object* v_jobs_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Elab_Term_TermElabM_parIter(v_00_u03b1_1800_, v_jobs_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
return v_res_1809_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1810_, v___x_1818_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1838_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1838_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1838_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v_fst_1825_; lean_object* v_snd_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1837_; 
v___x_1824_ = l_List_unzipTR___redArg(v_a_1820_);
v_fst_1825_ = lean_ctor_get(v___x_1824_, 0);
v_snd_1826_ = lean_ctor_get(v___x_1824_, 1);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1828_ = v___x_1824_;
v_isShared_1829_ = v_isSharedCheck_1837_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_snd_1826_);
lean_inc(v_fst_1825_);
lean_dec(v___x_1824_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1837_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1830_, 0, v_fst_1825_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_snd_1826_);
v___x_1832_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1832_);
v___x_1834_ = v___x_1822_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
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
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1819_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1819_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1810_ = stack[0].m_obj;
lean_object* v_a_1811_ = stack[1].m_obj;
lean_object* v_a_1812_ = stack[2].m_obj;
lean_object* v_a_1813_ = stack[3].m_obj;
lean_object* v_a_1814_ = stack[4].m_obj;
lean_object* v_a_1815_ = stack[5].m_obj;
lean_object* v_a_1816_ = stack[6].m_obj;
lean_object* v_res_1847_;
v_res_1847_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
stack->m_obj
 = v_res_1847_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
return v_res_1856_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1857_, lean_object* v_jobs_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1858_ = stack[1].m_obj;
lean_object* v_a_1859_ = stack[2].m_obj;
lean_object* v_a_1860_ = stack[3].m_obj;
lean_object* v_a_1861_ = stack[4].m_obj;
lean_object* v_a_1862_ = stack[5].m_obj;
lean_object* v_a_1863_ = stack[6].m_obj;
lean_object* v_a_1864_ = stack[7].m_obj;
lean_object* v_res_1867_;
v_res_1867_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(lean_box(0), v_jobs_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_);
stack->m_obj
 = v_res_1867_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_jobs_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(v_00_u03b1_1868_, v_jobs_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
return v_res_1877_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(lean_object* v_jobs_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1895_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1895_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_snd_1891_; lean_object* v___x_1893_; 
v_snd_1891_ = lean_ctor_get(v_a_1887_, 1);
lean_inc(v_snd_1891_);
lean_dec(v_a_1887_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v_snd_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_snd_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
v_a_1896_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1886_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1886_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1878_ = stack[0].m_obj;
lean_object* v_a_1879_ = stack[1].m_obj;
lean_object* v_a_1880_ = stack[2].m_obj;
lean_object* v_a_1881_ = stack[3].m_obj;
lean_object* v_a_1882_ = stack[4].m_obj;
lean_object* v_a_1883_ = stack[5].m_obj;
lean_object* v_a_1884_ = stack[6].m_obj;
lean_object* v_res_1904_;
v_res_1904_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
stack->m_obj
 = v_res_1904_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
return v_res_1913_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy(lean_object* v_00_u03b1_1914_, lean_object* v_jobs_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
return v___x_1923_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parIterGreedy_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_1915_ = stack[1].m_obj;
lean_object* v_a_1916_ = stack[2].m_obj;
lean_object* v_a_1917_ = stack[3].m_obj;
lean_object* v_a_1918_ = stack[4].m_obj;
lean_object* v_a_1919_ = stack[5].m_obj;
lean_object* v_a_1920_ = stack[6].m_obj;
lean_object* v_a_1921_ = stack[7].m_obj;
lean_object* v_res_1924_;
v_res_1924_ = l_Lean_Elab_Term_TermElabM_parIterGreedy(lean_box(0), v_jobs_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
stack->m_obj
 = v_res_1924_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_jobs_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Elab_Term_TermElabM_parIterGreedy(v_00_u03b1_1925_, v_jobs_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
return v_res_1934_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(lean_object* v_x_1935_, lean_object* v_x_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
if (lean_obj_tag(v_x_1935_) == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = l_List_reverse___redArg(v_x_1936_);
v___x_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
return v___x_1945_;
}
else
{
lean_object* v_head_1946_; lean_object* v_tail_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1965_; 
v_head_1946_ = lean_ctor_get(v_x_1935_, 0);
v_tail_1947_ = lean_ctor_get(v_x_1935_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_x_1935_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1949_ = v_x_1935_;
v_isShared_1950_ = v_isSharedCheck_1965_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_tail_1947_);
lean_inc(v_head_1946_);
lean_dec(v_x_1935_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1965_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_head_1946_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v_x_1936_);
lean_ctor_set(v___x_1949_, 0, v_a_1952_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1952_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_x_1936_);
v___x_1954_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
v_x_1935_ = v_tail_1947_;
v_x_1936_ = v___x_1954_;
goto _start;
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_del_object(v___x_1949_);
lean_dec(v_tail_1947_);
lean_dec(v_x_1936_);
v_a_1957_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1951_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1951_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1935_ = stack[0].m_obj;
lean_object* v_x_1936_ = stack[1].m_obj;
lean_object* v___y_1937_ = stack[2].m_obj;
lean_object* v___y_1938_ = stack[3].m_obj;
lean_object* v___y_1939_ = stack[4].m_obj;
lean_object* v___y_1940_ = stack[5].m_obj;
lean_object* v___y_1941_ = stack[6].m_obj;
lean_object* v___y_1942_ = stack[7].m_obj;
lean_object* v_res_1966_;
v_res_1966_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_1935_, v_x_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
stack->m_obj
 = v_res_1966_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg___boxed(lean_object* v_x_1967_, lean_object* v_x_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_1967_, v_x_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
return v_res_1976_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(lean_object* v_as_x27_1977_, lean_object* v_b_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
if (lean_obj_tag(v_as_x27_1977_) == 0)
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_b_1978_);
return v___x_1986_;
}
else
{
lean_object* v_head_1987_; lean_object* v_tail_1988_; lean_object* v___y_1990_; uint8_t v___y_1991_; lean_object* v_a_1997_; lean_object* v___x_2989__overap_2000_; lean_object* v___x_2001_; 
v_head_1987_ = lean_ctor_get(v_as_x27_1977_, 0);
v_tail_1988_ = lean_ctor_get(v_as_x27_1977_, 1);
lean_inc(v_head_1987_);
v___x_2989__overap_2000_ = lean_task_get_own(v_head_1987_);
lean_inc(v___y_1984_);
lean_inc_ref(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc_ref(v___y_1981_);
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1979_);
v___x_2001_ = lean_apply_7(v___x_2989__overap_2000_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, lean_box(0));
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = l_Lean_Elab_Term_saveState___redArg(v___y_1980_, v___y_1982_, v___y_1984_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2014_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2014_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2014_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_a_2002_);
lean_ctor_set(v___x_2008_, 1, v_a_2004_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set_tag(v___x_2006_, 1);
lean_ctor_set(v___x_2006_, 0, v___x_2008_);
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v_b_1978_);
v_as_x27_1977_ = v_tail_1988_;
v_b_1978_ = v___x_2011_;
goto _start;
}
}
}
else
{
lean_object* v_a_2015_; 
lean_dec(v_a_2002_);
v_a_2015_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2003_, 1);
v_a_1997_ = v_a_2015_;
goto v___jp_1996_;
}
}
else
{
lean_object* v_a_2016_; 
v_a_2016_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2001_, 1);
v_a_1997_ = v_a_2016_;
goto v___jp_1996_;
}
v___jp_1989_:
{
if (v___y_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___y_1990_);
v___x_1993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v_b_1978_);
v_as_x27_1977_ = v_tail_1988_;
v_b_1978_ = v___x_1993_;
goto _start;
}
else
{
lean_object* v___x_1995_; 
lean_dec(v_b_1978_);
v___x_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1995_, 0, v___y_1990_);
return v___x_1995_;
}
}
v___jp_1996_:
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Exception_isInterrupt(v_a_1997_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; 
lean_inc_ref(v_a_1997_);
v___x_1999_ = l_Lean_Exception_isRuntime(v_a_1997_);
v___y_1990_ = v_a_1997_;
v___y_1991_ = v___x_1999_;
goto v___jp_1989_;
}
else
{
v___y_1990_ = v_a_1997_;
v___y_1991_ = v___x_1998_;
goto v___jp_1989_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1977_ = stack[0].m_obj;
lean_object* v_b_1978_ = stack[1].m_obj;
lean_object* v___y_1979_ = stack[2].m_obj;
lean_object* v___y_1980_ = stack[3].m_obj;
lean_object* v___y_1981_ = stack[4].m_obj;
lean_object* v___y_1982_ = stack[5].m_obj;
lean_object* v___y_1983_ = stack[6].m_obj;
lean_object* v___y_1984_ = stack[7].m_obj;
lean_object* v_res_2017_;
v_res_2017_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_1977_, v_b_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
stack->m_obj
 = v_res_2017_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg___boxed(lean_object* v_as_x27_2018_, lean_object* v_b_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_2018_, v_b_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v_as_x27_2018_);
return v_res_2027_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_par___redArg(lean_object* v_jobs_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_st_ref_get(v_a_2030_);
v___x_2037_ = lean_box(0);
v___x_2038_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_2028_, v___x_2037_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_a_2039_, v___x_2037_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
lean_dec(v_a_2039_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2050_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2050_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = lean_st_ref_swap(v_a_2030_, v___x_2036_);
lean_dec(v___x_2045_);
v___x_2046_ = l_List_reverse___redArg(v_a_2041_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2046_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_dec(v___x_2036_);
return v___x_2040_;
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v___x_2036_);
v_a_2051_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2038_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2038_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_par___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2028_ = stack[0].m_obj;
lean_object* v_a_2029_ = stack[1].m_obj;
lean_object* v_a_2030_ = stack[2].m_obj;
lean_object* v_a_2031_ = stack[3].m_obj;
lean_object* v_a_2032_ = stack[4].m_obj;
lean_object* v_a_2033_ = stack[5].m_obj;
lean_object* v_a_2034_ = stack[6].m_obj;
lean_object* v_res_2059_;
v_res_2059_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
stack->m_obj
 = v_res_2059_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg___boxed(lean_object* v_jobs_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2068_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_par(lean_object* v_00_u03b1_2069_, lean_object* v_jobs_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_par_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2070_ = stack[1].m_obj;
lean_object* v_a_2071_ = stack[2].m_obj;
lean_object* v_a_2072_ = stack[3].m_obj;
lean_object* v_a_2073_ = stack[4].m_obj;
lean_object* v_a_2074_ = stack[5].m_obj;
lean_object* v_a_2075_ = stack[6].m_obj;
lean_object* v_a_2076_ = stack[7].m_obj;
lean_object* v_res_2079_;
v_res_2079_ = l_Lean_Elab_Term_TermElabM_par(lean_box(0), v_jobs_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
stack->m_obj
 = v_res_2079_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___boxed(lean_object* v_00_u03b1_2080_, lean_object* v_jobs_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Lean_Elab_Term_TermElabM_par(v_00_u03b1_2080_, v_jobs_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2089_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(lean_object* v_00_u03b1_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_2091_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
return v___x_2100_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2091_ = stack[1].m_obj;
lean_object* v_x_2092_ = stack[2].m_obj;
lean_object* v___y_2093_ = stack[3].m_obj;
lean_object* v___y_2094_ = stack[4].m_obj;
lean_object* v___y_2095_ = stack[5].m_obj;
lean_object* v___y_2096_ = stack[6].m_obj;
lean_object* v___y_2097_ = stack[7].m_obj;
lean_object* v___y_2098_ = stack[8].m_obj;
lean_object* v_res_2101_;
v_res_2101_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(lean_box(0), v_x_2091_, v_x_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
stack->m_obj
 = v_res_2101_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___boxed(lean_object* v_00_u03b1_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(v_00_u03b1_2102_, v_x_2103_, v_x_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2112_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(lean_object* v_00_u03b1_2113_, lean_object* v_as_2114_, lean_object* v_as_x27_2115_, lean_object* v_b_2116_, lean_object* v_a_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_2115_, v_b_2116_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2114_ = stack[1].m_obj;
lean_object* v_as_x27_2115_ = stack[2].m_obj;
lean_object* v_b_2116_ = stack[3].m_obj;
lean_object* v___y_2118_ = stack[5].m_obj;
lean_object* v___y_2119_ = stack[6].m_obj;
lean_object* v___y_2120_ = stack[7].m_obj;
lean_object* v___y_2121_ = stack[8].m_obj;
lean_object* v___y_2122_ = stack[9].m_obj;
lean_object* v___y_2123_ = stack[10].m_obj;
lean_object* v_res_2126_;
v_res_2126_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(lean_box(0), v_as_2114_, v_as_x27_2115_, v_b_2116_, lean_box(0), v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
stack->m_obj
 = v_res_2126_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_as_2128_, lean_object* v_as_x27_2129_, lean_object* v_b_2130_, lean_object* v_a_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(v_00_u03b1_2127_, v_as_2128_, v_as_x27_2129_, v_b_2130_, v_a_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_as_x27_2129_);
lean_dec(v_as_2128_);
return v_res_2139_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(lean_object* v_as_x27_2140_, lean_object* v_b_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
if (lean_obj_tag(v_as_x27_2140_) == 0)
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_b_2141_);
return v___x_2149_;
}
else
{
lean_object* v_head_2150_; lean_object* v_tail_2151_; lean_object* v___x_2599__overap_2152_; lean_object* v___x_2153_; 
v_head_2150_ = lean_ctor_get(v_as_x27_2140_, 0);
v_tail_2151_ = lean_ctor_get(v_as_x27_2140_, 1);
lean_inc(v_head_2150_);
v___x_2599__overap_2152_ = lean_task_get_own(v_head_2150_);
lean_inc(v___y_2147_);
lean_inc_ref(v___y_2146_);
lean_inc(v___y_2145_);
lean_inc_ref(v___y_2144_);
lean_inc(v___y_2143_);
lean_inc_ref(v___y_2142_);
v___x_2153_ = lean_apply_7(v___x_2599__overap_2152_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, lean_box(0));
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_a_2154_);
v___x_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v_b_2141_);
v_as_x27_2140_ = v_tail_2151_;
v_b_2141_ = v___x_2156_;
goto _start;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2172_; 
v_a_2158_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2160_ = v___x_2153_;
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2153_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
uint8_t v___y_2163_; uint8_t v___x_2170_; 
v___x_2170_ = l_Lean_Exception_isInterrupt(v_a_2158_);
if (v___x_2170_ == 0)
{
uint8_t v___x_2171_; 
lean_inc(v_a_2158_);
v___x_2171_ = l_Lean_Exception_isRuntime(v_a_2158_);
v___y_2163_ = v___x_2171_;
goto v___jp_2162_;
}
else
{
v___y_2163_ = v___x_2170_;
goto v___jp_2162_;
}
v___jp_2162_:
{
if (v___y_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_del_object(v___x_2160_);
v___x_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2164_, 0, v_a_2158_);
v___x_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2164_);
lean_ctor_set(v___x_2165_, 1, v_b_2141_);
v_as_x27_2140_ = v_tail_2151_;
v_b_2141_ = v___x_2165_;
goto _start;
}
else
{
lean_object* v___x_2168_; 
lean_dec(v_b_2141_);
if (v_isShared_2161_ == 0)
{
v___x_2168_ = v___x_2160_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2158_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2140_ = stack[0].m_obj;
lean_object* v_b_2141_ = stack[1].m_obj;
lean_object* v___y_2142_ = stack[2].m_obj;
lean_object* v___y_2143_ = stack[3].m_obj;
lean_object* v___y_2144_ = stack[4].m_obj;
lean_object* v___y_2145_ = stack[5].m_obj;
lean_object* v___y_2146_ = stack[6].m_obj;
lean_object* v___y_2147_ = stack[7].m_obj;
lean_object* v_res_2173_;
v_res_2173_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2140_, v_b_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
stack->m_obj
 = v_res_2173_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_2174_, lean_object* v_b_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2174_, v_b_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v_as_x27_2174_);
return v_res_2183_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg(lean_object* v_jobs_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_st_ref_get(v_a_2186_);
v___x_2193_ = lean_box(0);
v___x_2194_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_2184_, v___x_2193_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_a_2195_, v___x_2193_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2206_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2206_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2201_ = lean_st_ref_swap(v_a_2186_, v___x_2192_);
lean_dec(v___x_2201_);
v___x_2202_ = l_List_reverse___redArg(v_a_2197_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2202_);
v___x_2204_ = v___x_2199_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_dec(v___x_2192_);
return v___x_2196_;
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v___x_2192_);
v_a_2207_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2194_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2194_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_par_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2184_ = stack[0].m_obj;
lean_object* v_a_2185_ = stack[1].m_obj;
lean_object* v_a_2186_ = stack[2].m_obj;
lean_object* v_a_2187_ = stack[3].m_obj;
lean_object* v_a_2188_ = stack[4].m_obj;
lean_object* v_a_2189_ = stack[5].m_obj;
lean_object* v_a_2190_ = stack[6].m_obj;
lean_object* v_res_2215_;
v_res_2215_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg___boxed(lean_object* v_jobs_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2224_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_par_x27(lean_object* v_00_u03b1_2225_, lean_object* v_jobs_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2234_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_par_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2226_ = stack[1].m_obj;
lean_object* v_a_2227_ = stack[2].m_obj;
lean_object* v_a_2228_ = stack[3].m_obj;
lean_object* v_a_2229_ = stack[4].m_obj;
lean_object* v_a_2230_ = stack[5].m_obj;
lean_object* v_a_2231_ = stack[6].m_obj;
lean_object* v_a_2232_ = stack[7].m_obj;
lean_object* v_res_2235_;
v_res_2235_ = l_Lean_Elab_Term_TermElabM_par_x27(lean_box(0), v_jobs_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
stack->m_obj
 = v_res_2235_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_jobs_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Elab_Term_TermElabM_par_x27(v_00_u03b1_2236_, v_jobs_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
lean_dec(v_a_2243_);
lean_dec_ref(v_a_2242_);
lean_dec(v_a_2241_);
lean_dec_ref(v_a_2240_);
lean_dec(v_a_2239_);
lean_dec_ref(v_a_2238_);
return v_res_2245_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(lean_object* v_00_u03b1_2246_, lean_object* v_as_2247_, lean_object* v_as_x27_2248_, lean_object* v_b_2249_, lean_object* v_a_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2248_, v_b_2249_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2247_ = stack[1].m_obj;
lean_object* v_as_x27_2248_ = stack[2].m_obj;
lean_object* v_b_2249_ = stack[3].m_obj;
lean_object* v___y_2251_ = stack[5].m_obj;
lean_object* v___y_2252_ = stack[6].m_obj;
lean_object* v___y_2253_ = stack[7].m_obj;
lean_object* v___y_2254_ = stack[8].m_obj;
lean_object* v___y_2255_ = stack[9].m_obj;
lean_object* v___y_2256_ = stack[10].m_obj;
lean_object* v_res_2259_;
v_res_2259_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(lean_box(0), v_as_2247_, v_as_x27_2248_, v_b_2249_, lean_box(0), v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
stack->m_obj
 = v_res_2259_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_2260_, lean_object* v_as_2261_, lean_object* v_as_x27_2262_, lean_object* v_b_2263_, lean_object* v_a_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(v_00_u03b1_2260_, v_as_2261_, v_as_x27_2262_, v_b_2263_, v_a_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_as_x27_2262_);
lean_dec(v_as_2261_);
return v_res_2272_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_box(1);
v___x_2274_ = l_Lean_MessageData_ofFormat(v___x_2273_);
return v___x_2274_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2));
v___x_2279_ = l_Lean_MessageData_ofFormat(v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
if (lean_obj_tag(v_x_2281_) == 0)
{
return v_x_2280_;
}
else
{
lean_object* v_head_2282_; lean_object* v_tail_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2305_; 
v_head_2282_ = lean_ctor_get(v_x_2281_, 0);
v_tail_2283_ = lean_ctor_get(v_x_2281_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_x_2281_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2285_ = v_x_2281_;
v_isShared_2286_ = v_isSharedCheck_2305_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_tail_2283_);
lean_inc(v_head_2282_);
lean_dec(v_x_2281_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2305_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_before_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2303_; 
v_before_2287_ = lean_ctor_get(v_head_2282_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_head_2282_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v_head_2282_, 1);
lean_dec(v_unused_2304_);
v___x_2289_ = v_head_2282_;
v_isShared_2290_ = v_isSharedCheck_2303_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_before_2287_);
lean_dec(v_head_2282_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2303_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2290_ == 0)
{
lean_ctor_set_tag(v___x_2289_, 7);
lean_ctor_set(v___x_2289_, 1, v___x_2291_);
lean_ctor_set(v___x_2289_, 0, v_x_2280_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_x_2280_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2294_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_2286_ == 0)
{
lean_ctor_set_tag(v___x_2285_, 7);
lean_ctor_set(v___x_2285_, 1, v___x_2294_);
lean_ctor_set(v___x_2285_, 0, v___x_2293_);
v___x_2296_ = v___x_2285_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = l_Lean_MessageData_ofSyntax(v_before_2287_);
v___x_2298_ = l_Lean_indentD(v___x_2297_);
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2296_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v_x_2280_ = v___x_2299_;
v_x_2281_ = v_tail_2283_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(lean_object* v_opts_2306_, lean_object* v_opt_2307_){
_start:
{
lean_object* v_name_2308_; lean_object* v_defValue_2309_; lean_object* v_map_2310_; lean_object* v___x_2311_; 
v_name_2308_ = lean_ctor_get(v_opt_2307_, 0);
v_defValue_2309_ = lean_ctor_get(v_opt_2307_, 1);
v_map_2310_ = lean_ctor_get(v_opts_2306_, 0);
v___x_2311_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2310_, v_name_2308_);
if (lean_obj_tag(v___x_2311_) == 0)
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_unbox(v_defValue_2309_);
return v___x_2312_;
}
else
{
lean_object* v_val_2313_; 
v_val_2313_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_val_2313_);
lean_dec_ref_known(v___x_2311_, 1);
if (lean_obj_tag(v_val_2313_) == 1)
{
uint8_t v_v_2314_; 
v_v_2314_ = lean_ctor_get_uint8(v_val_2313_, 0);
lean_dec_ref_known(v_val_2313_, 0);
return v_v_2314_;
}
else
{
uint8_t v___x_2315_; 
lean_dec(v_val_2313_);
v___x_2315_ = lean_unbox(v_defValue_2309_);
return v___x_2315_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2306_ = stack[0].m_obj;
lean_object* v_opt_2307_ = stack[1].m_obj;
uint8_t v_res_2316_;
v_res_2316_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_opts_2306_, v_opt_2307_);
stack->m_num = v_res_2316_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2___boxed(lean_object* v_opts_2317_, lean_object* v_opt_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_opts_2317_, v_opt_2318_);
lean_dec_ref(v_opt_2318_);
lean_dec_ref(v_opts_2317_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1));
v___x_2325_ = l_Lean_MessageData_ofFormat(v___x_2324_);
return v___x_2325_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(lean_object* v_msgData_2326_, lean_object* v_macroStack_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2330_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2328_);
v___x_2331_ = l_Lean_Elab_pp_macroStack;
v___x_2332_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v___x_2330_, v___x_2331_);
lean_dec_ref(v___x_2330_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_dec(v_macroStack_2327_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_msgData_2326_);
return v___x_2333_;
}
else
{
if (lean_obj_tag(v_macroStack_2327_) == 0)
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_msgData_2326_);
return v___x_2334_;
}
else
{
lean_object* v_head_2335_; lean_object* v_after_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2351_; 
v_head_2335_ = lean_ctor_get(v_macroStack_2327_, 0);
lean_inc(v_head_2335_);
v_after_2336_ = lean_ctor_get(v_head_2335_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_head_2335_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v_head_2335_, 0);
lean_dec(v_unused_2352_);
v___x_2338_ = v_head_2335_;
v_isShared_2339_ = v_isSharedCheck_2351_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_after_2336_);
lean_dec(v_head_2335_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2351_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2340_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2339_ == 0)
{
lean_ctor_set_tag(v___x_2338_, 7);
lean_ctor_set(v___x_2338_, 1, v___x_2340_);
lean_ctor_set(v___x_2338_, 0, v_msgData_2326_);
v___x_2342_ = v___x_2338_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_msgData_2326_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v_msgData_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2343_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_MessageData_ofSyntax(v_after_2336_);
v___x_2346_ = l_Lean_indentD(v___x_2345_);
v_msgData_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2347_, 0, v___x_2344_);
lean_ctor_set(v_msgData_2347_, 1, v___x_2346_);
v___x_2348_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(v_msgData_2347_, v_macroStack_2327_);
v___x_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2348_);
return v___x_2349_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2326_ = stack[0].m_obj;
lean_object* v_macroStack_2327_ = stack[1].m_obj;
lean_object* v___y_2328_ = stack[2].m_obj;
lean_object* v_res_2353_;
v_res_2353_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2326_, v_macroStack_2327_, v___y_2328_);
stack->m_obj
 = v_res_2353_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2354_, lean_object* v_macroStack_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2354_, v_macroStack_2355_, v___y_2356_);
lean_dec_ref(v___y_2356_);
return v_res_2358_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_ref_2367_; lean_object* v_macroStack_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_a_2371_; lean_object* v___x_2372_; lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2381_; 
v_ref_2367_ = lean_ctor_get(v___y_2364_, 2);
v_macroStack_2368_ = lean_ctor_get(v___y_2360_, 1);
v___x_2369_ = l_Lean_Elab_getBetterRef(v_ref_2367_, v_macroStack_2368_);
v___x_2370_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_2359_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
lean_inc(v_a_2371_);
lean_dec_ref(v___x_2370_);
lean_inc(v_macroStack_2368_);
v___x_2372_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_a_2371_, v_macroStack_2368_, v___y_2364_);
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2375_ = v___x_2372_;
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2381_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2369_);
lean_ctor_set(v___x_2377_, 1, v_a_2373_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set_tag(v___x_2375_, 1);
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2359_ = stack[0].m_obj;
lean_object* v___y_2360_ = stack[1].m_obj;
lean_object* v___y_2361_ = stack[2].m_obj;
lean_object* v___y_2362_ = stack[3].m_obj;
lean_object* v___y_2363_ = stack[4].m_obj;
lean_object* v___y_2364_ = stack[5].m_obj;
lean_object* v___y_2365_ = stack[6].m_obj;
lean_object* v_res_2382_;
v_res_2382_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
stack->m_obj
 = v_res_2382_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
return v_res_2391_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_2392_, lean_object* v___x_2393_, lean_object* v_____r_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v_a_2392_);
v___x_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v___x_2393_);
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2392_ = stack[0].m_obj;
lean_object* v___x_2393_ = stack[1].m_obj;
lean_object* v_____r_2394_ = stack[2].m_obj;
lean_object* v___y_2395_ = stack[3].m_obj;
lean_object* v___y_2396_ = stack[4].m_obj;
lean_object* v___y_2397_ = stack[5].m_obj;
lean_object* v___y_2398_ = stack[6].m_obj;
lean_object* v___y_2399_ = stack[7].m_obj;
lean_object* v___y_2400_ = stack[8].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2392_, v___x_2393_, v_____r_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_2407_, lean_object* v___x_2408_, lean_object* v_____r_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2407_, v___x_2408_, v_____r_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
return v_res_2417_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(uint8_t v_cancel_2418_, lean_object* v_fst_2419_, lean_object* v_a_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
if (lean_obj_tag(v_a_2420_) == 0)
{
lean_object* v___x_2429_; 
lean_dec_ref(v_fst_2419_);
v___x_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_b_2421_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_fst_2433_; lean_object* v_snd_2434_; lean_object* v___y_2436_; lean_object* v___x_2456_; 
lean_dec_ref(v_b_2421_);
v___x_2430_ = lean_box(0);
v___x_2431_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2432_ = l_IO_waitAny_x27___redArg(v_a_2420_);
v_fst_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_fst_2433_);
v_snd_2434_ = lean_ctor_get(v___x_2432_, 1);
lean_inc(v_snd_2434_);
lean_dec_ref(v___x_2432_);
lean_inc(v___y_2427_);
lean_inc_ref(v___y_2426_);
lean_inc(v___y_2425_);
lean_inc_ref(v___y_2424_);
lean_inc(v___y_2423_);
lean_inc_ref(v___y_2422_);
v___x_2456_ = lean_apply_7(v_fst_2433_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, lean_box(0));
if (lean_obj_tag(v___x_2456_) == 0)
{
if (v_cancel_2418_ == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2458_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2457_, v___x_2430_, v___x_2430_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
v___y_2436_ = v___x_2458_;
goto v___jp_2435_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_a_2459_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2456_, 1);
lean_inc_ref(v_fst_2419_);
v___x_2460_ = lean_apply_1(v_fst_2419_, lean_box(0));
v___x_2461_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2459_, v___x_2430_, v___x_2460_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
v___y_2436_ = v___x_2461_;
goto v___jp_2435_;
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2474_; 
v_a_2462_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2464_ = v___x_2456_;
v_isShared_2465_ = v_isSharedCheck_2474_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2456_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2474_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
uint8_t v___y_2467_; uint8_t v___x_2472_; 
v___x_2472_ = l_Lean_Exception_isInterrupt(v_a_2462_);
if (v___x_2472_ == 0)
{
uint8_t v___x_2473_; 
lean_inc(v_a_2462_);
v___x_2473_ = l_Lean_Exception_isRuntime(v_a_2462_);
v___y_2467_ = v___x_2473_;
goto v___jp_2466_;
}
else
{
v___y_2467_ = v___x_2472_;
goto v___jp_2466_;
}
v___jp_2466_:
{
if (v___y_2467_ == 0)
{
lean_del_object(v___x_2464_);
lean_dec(v_a_2462_);
v_a_2420_ = v_snd_2434_;
v_b_2421_ = v___x_2431_;
goto _start;
}
else
{
lean_object* v___x_2470_; 
lean_dec(v_snd_2434_);
lean_dec_ref(v_fst_2419_);
if (v_isShared_2465_ == 0)
{
v___x_2470_ = v___x_2464_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2462_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
v___jp_2435_:
{
if (lean_obj_tag(v___y_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2447_; 
v_a_2437_ = lean_ctor_get(v___y_2436_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___y_2436_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2439_ = v___y_2436_;
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___y_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2447_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
if (lean_obj_tag(v_a_2437_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; 
lean_dec(v_snd_2434_);
lean_dec_ref(v_fst_2419_);
v_a_2441_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v_a_2437_, 1);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v_a_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
else
{
lean_object* v_a_2445_; 
lean_del_object(v___x_2439_);
v_a_2445_ = lean_ctor_get(v_a_2437_, 0);
lean_inc(v_a_2445_);
lean_dec_ref_known(v_a_2437_, 1);
v_a_2420_ = v_snd_2434_;
v_b_2421_ = v_a_2445_;
goto _start;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_snd_2434_);
lean_dec_ref(v_fst_2419_);
v_a_2448_ = lean_ctor_get(v___y_2436_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___y_2436_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___y_2436_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___y_2436_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_2418_ = stack[0].m_num;
lean_object* v_fst_2419_ = stack[1].m_obj;
lean_object* v_a_2420_ = stack[2].m_obj;
lean_object* v_b_2421_ = stack[3].m_obj;
lean_object* v___y_2422_ = stack[4].m_obj;
lean_object* v___y_2423_ = stack[5].m_obj;
lean_object* v___y_2424_ = stack[6].m_obj;
lean_object* v___y_2425_ = stack[7].m_obj;
lean_object* v___y_2426_ = stack[8].m_obj;
lean_object* v___y_2427_ = stack[9].m_obj;
lean_object* v_res_2475_;
v_res_2475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2418_, v_fst_2419_, v_a_2420_, v_b_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
stack->m_obj
 = v_res_2475_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_2476_, lean_object* v_fst_2477_, lean_object* v_a_2478_, lean_object* v_b_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
uint8_t v_cancel_boxed_2487_; lean_object* v_res_2488_; 
v_cancel_boxed_2487_ = lean_unbox(v_cancel_2476_);
v_res_2488_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_boxed_2487_, v_fst_2477_, v_a_2478_, v_b_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2488_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg(lean_object* v_jobs_2489_, uint8_t v_cancel_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_2489_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v_fst_2500_; lean_object* v_snd_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v_fst_2500_ = lean_ctor_get(v_a_2499_, 0);
lean_inc(v_fst_2500_);
v_snd_2501_ = lean_ctor_get(v_a_2499_, 1);
lean_inc(v_snd_2501_);
lean_dec(v_a_2499_);
v___x_2502_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2490_, v_fst_2500_, v_snd_2501_, v___x_2502_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2515_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2506_ = v___x_2503_;
v_isShared_2507_ = v_isSharedCheck_2515_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2515_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v_fst_2508_; 
v_fst_2508_ = lean_ctor_get(v_a_2504_, 0);
lean_inc(v_fst_2508_);
lean_dec(v_a_2504_);
if (lean_obj_tag(v_fst_2508_) == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_del_object(v___x_2506_);
v___x_2509_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_2510_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v___x_2509_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
return v___x_2510_;
}
else
{
lean_object* v_val_2511_; lean_object* v___x_2513_; 
v_val_2511_ = lean_ctor_get(v_fst_2508_, 0);
lean_inc(v_val_2511_);
lean_dec_ref_known(v_fst_2508_, 1);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v_val_2511_);
v___x_2513_ = v___x_2506_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_val_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_a_2516_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2503_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2503_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2524_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2498_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2498_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parFirst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2489_ = stack[0].m_obj;
uint8_t v_cancel_2490_ = stack[1].m_num;
lean_object* v_a_2491_ = stack[2].m_obj;
lean_object* v_a_2492_ = stack[3].m_obj;
lean_object* v_a_2493_ = stack[4].m_obj;
lean_object* v_a_2494_ = stack[5].m_obj;
lean_object* v_a_2495_ = stack[6].m_obj;
lean_object* v_a_2496_ = stack[7].m_obj;
lean_object* v_res_2532_;
v_res_2532_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2489_, v_cancel_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
stack->m_obj
 = v_res_2532_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg___boxed(lean_object* v_jobs_2533_, lean_object* v_cancel_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
uint8_t v_cancel_boxed_2542_; lean_object* v_res_2543_; 
v_cancel_boxed_2542_ = lean_unbox(v_cancel_2534_);
v_res_2543_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2533_, v_cancel_boxed_2542_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
return v_res_2543_;
}
}
lean_object* l_Lean_Elab_Term_TermElabM_parFirst(lean_object* v_00_u03b1_2544_, lean_object* v_jobs_2545_, uint8_t v_cancel_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2545_, v_cancel_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT void l_Lean_Elab_Term_TermElabM_parFirst_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2545_ = stack[1].m_obj;
uint8_t v_cancel_2546_ = stack[2].m_num;
lean_object* v_a_2547_ = stack[3].m_obj;
lean_object* v_a_2548_ = stack[4].m_obj;
lean_object* v_a_2549_ = stack[5].m_obj;
lean_object* v_a_2550_ = stack[6].m_obj;
lean_object* v_a_2551_ = stack[7].m_obj;
lean_object* v_a_2552_ = stack[8].m_obj;
lean_object* v_res_2555_;
v_res_2555_ = l_Lean_Elab_Term_TermElabM_parFirst(lean_box(0), v_jobs_2545_, v_cancel_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
stack->m_obj
 = v_res_2555_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___boxed(lean_object* v_00_u03b1_2556_, lean_object* v_jobs_2557_, lean_object* v_cancel_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
uint8_t v_cancel_boxed_2566_; lean_object* v_res_2567_; 
v_cancel_boxed_2566_ = lean_unbox(v_cancel_2558_);
v_res_2567_ = l_Lean_Elab_Term_TermElabM_parFirst(v_00_u03b1_2556_, v_jobs_2557_, v_cancel_boxed_2566_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
return v_res_2567_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(lean_object* v_00_u03b1_2568_, uint8_t v_cancel_2569_, lean_object* v_fst_2570_, lean_object* v_inst_2571_, lean_object* v_R_2572_, lean_object* v_a_2573_, lean_object* v_b_2574_, lean_object* v_c_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2569_, v_fst_2570_, v_a_2573_, v_b_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_2569_ = stack[1].m_num;
lean_object* v_fst_2570_ = stack[2].m_obj;
lean_object* v_a_2573_ = stack[5].m_obj;
lean_object* v_b_2574_ = stack[6].m_obj;
lean_object* v___y_2576_ = stack[8].m_obj;
lean_object* v___y_2577_ = stack[9].m_obj;
lean_object* v___y_2578_ = stack[10].m_obj;
lean_object* v___y_2579_ = stack[11].m_obj;
lean_object* v___y_2580_ = stack[12].m_obj;
lean_object* v___y_2581_ = stack[13].m_obj;
lean_object* v_res_2584_;
v_res_2584_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(lean_box(0), v_cancel_2569_, v_fst_2570_, lean_box(0), lean_box(0), v_a_2573_, v_b_2574_, lean_box(0), v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
stack->m_obj
 = v_res_2584_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_2585_, lean_object* v_cancel_2586_, lean_object* v_fst_2587_, lean_object* v_inst_2588_, lean_object* v_R_2589_, lean_object* v_a_2590_, lean_object* v_b_2591_, lean_object* v_c_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
uint8_t v_cancel_boxed_2600_; lean_object* v_res_2601_; 
v_cancel_boxed_2600_ = lean_unbox(v_cancel_2586_);
v_res_2601_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(v_00_u03b1_2585_, v_cancel_boxed_2600_, v_fst_2587_, v_inst_2588_, v_R_2589_, v_a_2590_, v_b_2591_, v_c_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
return v_res_2601_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(lean_object* v_00_u03b1_2602_, lean_object* v_msg_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
return v___x_2611_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2603_ = stack[1].m_obj;
lean_object* v___y_2604_ = stack[2].m_obj;
lean_object* v___y_2605_ = stack[3].m_obj;
lean_object* v___y_2606_ = stack[4].m_obj;
lean_object* v___y_2607_ = stack[5].m_obj;
lean_object* v___y_2608_ = stack[6].m_obj;
lean_object* v___y_2609_ = stack[7].m_obj;
lean_object* v_res_2612_;
v_res_2612_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(lean_box(0), v_msg_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
stack->m_obj
 = v_res_2612_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(v_00_u03b1_2613_, v_msg_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
return v_res_2622_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(lean_object* v_msgData_2623_, lean_object* v_macroStack_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2623_, v_macroStack_2624_, v___y_2629_);
return v___x_2632_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2623_ = stack[0].m_obj;
lean_object* v_macroStack_2624_ = stack[1].m_obj;
lean_object* v___y_2625_ = stack[2].m_obj;
lean_object* v___y_2626_ = stack[3].m_obj;
lean_object* v___y_2627_ = stack[4].m_obj;
lean_object* v___y_2628_ = stack[5].m_obj;
lean_object* v___y_2629_ = stack[6].m_obj;
lean_object* v___y_2630_ = stack[7].m_obj;
lean_object* v_res_2633_;
v_res_2633_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(v_msgData_2623_, v_macroStack_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
stack->m_obj
 = v_res_2633_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_2634_, lean_object* v_macroStack_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(v_msgData_2634_, v_macroStack_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2643_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(lean_object* v_x_2644_, lean_object* v_x_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
if (lean_obj_tag(v_x_2644_) == 0)
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = l_List_reverse___redArg(v_x_2645_);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
return v___x_2656_;
}
else
{
lean_object* v_head_2657_; lean_object* v_tail_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2676_; 
v_head_2657_ = lean_ctor_get(v_x_2644_, 0);
v_tail_2658_ = lean_ctor_get(v_x_2644_, 1);
v_isSharedCheck_2676_ = !lean_is_exclusive(v_x_2644_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2660_ = v_x_2644_;
v_isShared_2661_ = v_isSharedCheck_2676_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_tail_2658_);
lean_inc(v_head_2657_);
lean_dec(v_x_2644_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2676_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; 
v___x_2662_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_head_2657_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 1, v_x_2645_);
lean_ctor_set(v___x_2660_, 0, v_a_2663_);
v___x_2665_ = v___x_2660_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2663_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_x_2645_);
v___x_2665_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
v_x_2644_ = v_tail_2658_;
v_x_2645_ = v___x_2665_;
goto _start;
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_del_object(v___x_2660_);
lean_dec(v_tail_2658_);
lean_dec(v_x_2645_);
v_a_2668_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2662_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2662_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2644_ = stack[0].m_obj;
lean_object* v_x_2645_ = stack[1].m_obj;
lean_object* v___y_2646_ = stack[2].m_obj;
lean_object* v___y_2647_ = stack[3].m_obj;
lean_object* v___y_2648_ = stack[4].m_obj;
lean_object* v___y_2649_ = stack[5].m_obj;
lean_object* v___y_2650_ = stack[6].m_obj;
lean_object* v___y_2651_ = stack[7].m_obj;
lean_object* v___y_2652_ = stack[8].m_obj;
lean_object* v___y_2653_ = stack[9].m_obj;
lean_object* v_res_2677_;
v_res_2677_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2644_, v_x_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
stack->m_obj
 = v_res_2677_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_2678_, lean_object* v_x_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2678_, v_x_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2689_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(lean_object* v_jobs_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_box(0);
v___x_2701_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2690_, v___x_2700_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2720_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2720_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2720_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2706_; lean_object* v_fst_2707_; lean_object* v_snd_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2719_; 
v___x_2706_ = l_List_unzipTR___redArg(v_a_2702_);
v_fst_2707_ = lean_ctor_get(v___x_2706_, 0);
v_snd_2708_ = lean_ctor_get(v___x_2706_, 1);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2710_ = v___x_2706_;
v_isShared_2711_ = v_isSharedCheck_2719_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_snd_2708_);
lean_inc(v_fst_2707_);
lean_dec(v___x_2706_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2719_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2712_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2712_, 0, v_fst_2707_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2714_ = v___x_2710_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_snd_2708_);
v___x_2714_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2716_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2714_);
v___x_2716_ = v___x_2704_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v___x_2714_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
else
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2728_; 
v_a_2721_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2723_ = v___x_2701_;
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2701_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2728_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2726_; 
if (v_isShared_2724_ == 0)
{
v___x_2726_ = v___x_2723_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2690_ = stack[0].m_obj;
lean_object* v_a_2691_ = stack[1].m_obj;
lean_object* v_a_2692_ = stack[2].m_obj;
lean_object* v_a_2693_ = stack[3].m_obj;
lean_object* v_a_2694_ = stack[4].m_obj;
lean_object* v_a_2695_ = stack[5].m_obj;
lean_object* v_a_2696_ = stack[6].m_obj;
lean_object* v_a_2697_ = stack[7].m_obj;
lean_object* v_a_2698_ = stack[8].m_obj;
lean_object* v_res_2729_;
v_res_2729_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
stack->m_obj
 = v_res_2729_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2740_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel(lean_object* v_00_u03b1_2741_, lean_object* v_jobs_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
return v___x_2752_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIterWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2742_ = stack[1].m_obj;
lean_object* v_a_2743_ = stack[2].m_obj;
lean_object* v_a_2744_ = stack[3].m_obj;
lean_object* v_a_2745_ = stack[4].m_obj;
lean_object* v_a_2746_ = stack[5].m_obj;
lean_object* v_a_2747_ = stack[6].m_obj;
lean_object* v_a_2748_ = stack[7].m_obj;
lean_object* v_a_2749_ = stack[8].m_obj;
lean_object* v_a_2750_ = stack[9].m_obj;
lean_object* v_res_2753_;
v_res_2753_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel(lean_box(0), v_jobs_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
stack->m_obj
 = v_res_2753_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___boxed(lean_object* v_00_u03b1_2754_, lean_object* v_jobs_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel(v_00_u03b1_2754_, v_jobs_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
return v_res_2765_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_2766_, lean_object* v_x_2767_, lean_object* v_x_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2767_, v_x_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2767_ = stack[1].m_obj;
lean_object* v_x_2768_ = stack[2].m_obj;
lean_object* v___y_2769_ = stack[3].m_obj;
lean_object* v___y_2770_ = stack[4].m_obj;
lean_object* v___y_2771_ = stack[5].m_obj;
lean_object* v___y_2772_ = stack[6].m_obj;
lean_object* v___y_2773_ = stack[7].m_obj;
lean_object* v___y_2774_ = stack[8].m_obj;
lean_object* v___y_2775_ = stack[9].m_obj;
lean_object* v___y_2776_ = stack[10].m_obj;
lean_object* v_res_2779_;
v_res_2779_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(lean_box(0), v_x_2767_, v_x_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
stack->m_obj
 = v_res_2779_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_res_2792_; 
v_res_2792_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(v_00_u03b1_2780_, v_x_2781_, v_x_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2792_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg(lean_object* v_jobs_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2812_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2812_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2812_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v_snd_2808_; lean_object* v___x_2810_; 
v_snd_2808_ = lean_ctor_get(v_a_2804_, 1);
lean_inc(v_snd_2808_);
lean_dec(v_a_2804_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v_snd_2808_);
v___x_2810_ = v___x_2806_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_snd_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2803_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2803_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2793_ = stack[0].m_obj;
lean_object* v_a_2794_ = stack[1].m_obj;
lean_object* v_a_2795_ = stack[2].m_obj;
lean_object* v_a_2796_ = stack[3].m_obj;
lean_object* v_a_2797_ = stack[4].m_obj;
lean_object* v_a_2798_ = stack[5].m_obj;
lean_object* v_a_2799_ = stack[6].m_obj;
lean_object* v_a_2800_ = stack[7].m_obj;
lean_object* v_a_2801_ = stack[8].m_obj;
lean_object* v_res_2821_;
v_res_2821_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_);
stack->m_obj
 = v_res_2821_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg___boxed(lean_object* v_jobs_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
return v_res_2832_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIter(lean_object* v_00_u03b1_2833_, lean_object* v_jobs_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIter_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2834_ = stack[1].m_obj;
lean_object* v_a_2835_ = stack[2].m_obj;
lean_object* v_a_2836_ = stack[3].m_obj;
lean_object* v_a_2837_ = stack[4].m_obj;
lean_object* v_a_2838_ = stack[5].m_obj;
lean_object* v_a_2839_ = stack[6].m_obj;
lean_object* v_a_2840_ = stack[7].m_obj;
lean_object* v_a_2841_ = stack[8].m_obj;
lean_object* v_a_2842_ = stack[9].m_obj;
lean_object* v_res_2845_;
v_res_2845_ = l_Lean_Elab_Tactic_TacticM_parIter(lean_box(0), v_jobs_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_);
stack->m_obj
 = v_res_2845_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___boxed(lean_object* v_00_u03b1_2846_, lean_object* v_jobs_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_Elab_Tactic_TacticM_parIter(v_00_u03b1_2846_, v_jobs_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
return v_res_2857_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_box(0);
v___x_2869_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2858_, v___x_2868_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2888_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2888_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2888_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v_fst_2875_; lean_object* v_snd_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2887_; 
v___x_2874_ = l_List_unzipTR___redArg(v_a_2870_);
v_fst_2875_ = lean_ctor_get(v___x_2874_, 0);
v_snd_2876_ = lean_ctor_get(v___x_2874_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2878_ = v___x_2874_;
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_snd_2876_);
lean_inc(v_fst_2875_);
lean_dec(v___x_2874_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2880_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2880_, 0, v_fst_2875_);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2880_);
v___x_2882_ = v___x_2878_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2880_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v_snd_2876_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2882_);
v___x_2884_ = v___x_2872_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2869_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2869_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2858_ = stack[0].m_obj;
lean_object* v_a_2859_ = stack[1].m_obj;
lean_object* v_a_2860_ = stack[2].m_obj;
lean_object* v_a_2861_ = stack[3].m_obj;
lean_object* v_a_2862_ = stack[4].m_obj;
lean_object* v_a_2863_ = stack[5].m_obj;
lean_object* v_a_2864_ = stack[6].m_obj;
lean_object* v_a_2865_ = stack[7].m_obj;
lean_object* v_a_2866_ = stack[8].m_obj;
lean_object* v_res_2897_;
v_res_2897_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_);
stack->m_obj
 = v_res_2897_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_);
lean_dec(v_a_2906_);
lean_dec_ref(v_a_2905_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
return v_res_2908_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(lean_object* v_00_u03b1_2909_, lean_object* v_jobs_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
return v___x_2920_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2910_ = stack[1].m_obj;
lean_object* v_a_2911_ = stack[2].m_obj;
lean_object* v_a_2912_ = stack[3].m_obj;
lean_object* v_a_2913_ = stack[4].m_obj;
lean_object* v_a_2914_ = stack[5].m_obj;
lean_object* v_a_2915_ = stack[6].m_obj;
lean_object* v_a_2916_ = stack[7].m_obj;
lean_object* v_a_2917_ = stack[8].m_obj;
lean_object* v_a_2918_ = stack[9].m_obj;
lean_object* v_res_2921_;
v_res_2921_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(lean_box(0), v_jobs_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_);
stack->m_obj
 = v_res_2921_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_2922_, lean_object* v_jobs_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(v_00_u03b1_2922_, v_jobs_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec_ref(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_a_2924_);
return v_res_2933_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(lean_object* v_jobs_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2953_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v_snd_2949_; lean_object* v___x_2951_; 
v_snd_2949_ = lean_ctor_get(v_a_2945_, 1);
lean_inc(v_snd_2949_);
lean_dec(v_a_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v_snd_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_snd_2949_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
v_a_2954_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2944_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2944_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2934_ = stack[0].m_obj;
lean_object* v_a_2935_ = stack[1].m_obj;
lean_object* v_a_2936_ = stack[2].m_obj;
lean_object* v_a_2937_ = stack[3].m_obj;
lean_object* v_a_2938_ = stack[4].m_obj;
lean_object* v_a_2939_ = stack[5].m_obj;
lean_object* v_a_2940_ = stack[6].m_obj;
lean_object* v_a_2941_ = stack[7].m_obj;
lean_object* v_a_2942_ = stack[8].m_obj;
lean_object* v_res_2962_;
v_res_2962_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_);
stack->m_obj
 = v_res_2962_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg___boxed(lean_object* v_jobs_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
lean_dec(v_a_2971_);
lean_dec_ref(v_a_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_a_2968_);
lean_dec(v_a_2967_);
lean_dec_ref(v_a_2966_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
return v_res_2973_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy(lean_object* v_00_u03b1_2974_, lean_object* v_jobs_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_);
return v___x_2985_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parIterGreedy_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_2975_ = stack[1].m_obj;
lean_object* v_a_2976_ = stack[2].m_obj;
lean_object* v_a_2977_ = stack[3].m_obj;
lean_object* v_a_2978_ = stack[4].m_obj;
lean_object* v_a_2979_ = stack[5].m_obj;
lean_object* v_a_2980_ = stack[6].m_obj;
lean_object* v_a_2981_ = stack[7].m_obj;
lean_object* v_a_2982_ = stack[8].m_obj;
lean_object* v_a_2983_ = stack[9].m_obj;
lean_object* v_res_2986_;
v_res_2986_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy(lean_box(0), v_jobs_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_);
stack->m_obj
 = v_res_2986_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_jobs_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy(v_00_u03b1_2987_, v_jobs_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
return v_res_2998_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(lean_object* v_as_x27_2999_, lean_object* v_b_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
if (lean_obj_tag(v_as_x27_2999_) == 0)
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_b_3000_);
return v___x_3010_;
}
else
{
lean_object* v_head_3011_; lean_object* v_tail_3012_; lean_object* v___x_3013_; 
v_head_3011_ = lean_ctor_get(v_as_x27_2999_, 0);
v_tail_3012_ = lean_ctor_get(v_as_x27_2999_, 1);
v___x_3013_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3002_, v___y_3004_, v___y_3006_, v___y_3008_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3057_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3057_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3057_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___y_3019_; uint8_t v___y_3020_; lean_object* v_a_3037_; lean_object* v___x_2677__overap_3040_; lean_object* v___x_3041_; 
lean_inc(v_head_3011_);
v___x_2677__overap_3040_ = lean_task_get_own(v_head_3011_);
lean_inc(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc(v___y_3006_);
lean_inc_ref(v___y_3005_);
lean_inc(v___y_3004_);
lean_inc_ref(v___y_3003_);
lean_inc(v___y_3002_);
lean_inc_ref(v___y_3001_);
v___x_3041_ = lean_apply_9(v___x_2677__overap_3040_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, lean_box(0));
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_object* v_a_3042_; lean_object* v___x_3043_; 
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3002_, v___y_3004_, v___y_3006_, v___y_3008_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3054_; 
lean_del_object(v___x_3016_);
lean_dec(v_a_3014_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3054_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3048_, 0, v_a_3042_);
lean_ctor_set(v___x_3048_, 1, v_a_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 1);
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; 
v___x_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v_b_3000_);
v_as_x27_2999_ = v_tail_3012_;
v_b_3000_ = v___x_3051_;
goto _start;
}
}
}
else
{
lean_object* v_a_3055_; 
lean_dec(v_a_3042_);
v_a_3055_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3043_, 1);
v_a_3037_ = v_a_3055_;
goto v___jp_3036_;
}
}
else
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3041_, 1);
v_a_3037_ = v_a_3056_;
goto v___jp_3036_;
}
v___jp_3018_:
{
if (v___y_3020_ == 0)
{
lean_object* v___x_3021_; 
lean_del_object(v___x_3016_);
v___x_3021_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3014_, v___y_3020_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3021_, 1);
v___x_3022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3022_, 0, v___y_3019_);
v___x_3023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
lean_ctor_set(v___x_3023_, 1, v_b_3000_);
v_as_x27_2999_ = v_tail_3012_;
v_b_3000_ = v___x_3023_;
goto _start;
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec_ref(v___y_3019_);
lean_dec(v_b_3000_);
v_a_3025_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_3021_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3021_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
else
{
lean_object* v___x_3034_; 
lean_dec(v_a_3014_);
lean_dec(v_b_3000_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 1);
lean_ctor_set(v___x_3016_, 0, v___y_3019_);
v___x_3034_ = v___x_3016_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___y_3019_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
v___jp_3036_:
{
uint8_t v___x_3038_; 
v___x_3038_ = l_Lean_Exception_isInterrupt(v_a_3037_);
if (v___x_3038_ == 0)
{
uint8_t v___x_3039_; 
lean_inc_ref(v_a_3037_);
v___x_3039_ = l_Lean_Exception_isRuntime(v_a_3037_);
v___y_3019_ = v_a_3037_;
v___y_3020_ = v___x_3039_;
goto v___jp_3018_;
}
else
{
v___y_3019_ = v_a_3037_;
v___y_3020_ = v___x_3038_;
goto v___jp_3018_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_b_3000_);
v_a_3058_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3013_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3013_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_2999_ = stack[0].m_obj;
lean_object* v_b_3000_ = stack[1].m_obj;
lean_object* v___y_3001_ = stack[2].m_obj;
lean_object* v___y_3002_ = stack[3].m_obj;
lean_object* v___y_3003_ = stack[4].m_obj;
lean_object* v___y_3004_ = stack[5].m_obj;
lean_object* v___y_3005_ = stack[6].m_obj;
lean_object* v___y_3006_ = stack[7].m_obj;
lean_object* v___y_3007_ = stack[8].m_obj;
lean_object* v___y_3008_ = stack[9].m_obj;
lean_object* v_res_3066_;
v_res_3066_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_2999_, v_b_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
stack->m_obj
 = v_res_3066_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg___boxed(lean_object* v_as_x27_3067_, lean_object* v_b_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_3067_, v_b_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v_as_x27_3067_);
return v_res_3078_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(lean_object* v_x_3079_, lean_object* v_x_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
if (lean_obj_tag(v_x_3079_) == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = l_List_reverse___redArg(v_x_3080_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
else
{
lean_object* v_head_3092_; lean_object* v_tail_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3111_; 
v_head_3092_ = lean_ctor_get(v_x_3079_, 0);
v_tail_3093_ = lean_ctor_get(v_x_3079_, 1);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_x_3079_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3095_ = v_x_3079_;
v_isShared_3096_ = v_isSharedCheck_3111_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_tail_3093_);
lean_inc(v_head_3092_);
lean_dec(v_x_3079_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3111_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_head_3092_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 1, v_x_3080_);
lean_ctor_set(v___x_3095_, 0, v_a_3098_);
v___x_3100_ = v___x_3095_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3098_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_x_3080_);
v___x_3100_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
v_x_3079_ = v_tail_3093_;
v_x_3080_ = v___x_3100_;
goto _start;
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_del_object(v___x_3095_);
lean_dec(v_tail_3093_);
lean_dec(v_x_3080_);
v_a_3103_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3097_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3097_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3079_ = stack[0].m_obj;
lean_object* v_x_3080_ = stack[1].m_obj;
lean_object* v___y_3081_ = stack[2].m_obj;
lean_object* v___y_3082_ = stack[3].m_obj;
lean_object* v___y_3083_ = stack[4].m_obj;
lean_object* v___y_3084_ = stack[5].m_obj;
lean_object* v___y_3085_ = stack[6].m_obj;
lean_object* v___y_3086_ = stack[7].m_obj;
lean_object* v___y_3087_ = stack[8].m_obj;
lean_object* v___y_3088_ = stack[9].m_obj;
lean_object* v_res_3112_;
v_res_3112_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3079_, v_x_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
stack->m_obj
 = v_res_3112_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg___boxed(lean_object* v_x_3113_, lean_object* v_x_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3113_, v_x_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
return v_res_3124_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg(lean_object* v_jobs_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_st_ref_get(v_a_3127_);
v___x_3136_ = lean_box(0);
v___x_3137_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_jobs_3125_, v___x_3136_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3139_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_a_3138_, v___x_3136_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
lean_dec(v_a_3138_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3149_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3149_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3149_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3147_; 
v___x_3144_ = lean_st_ref_swap(v_a_3127_, v___x_3135_);
lean_dec(v___x_3144_);
v___x_3145_ = l_List_reverse___redArg(v_a_3140_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3145_);
v___x_3147_ = v___x_3142_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
else
{
lean_dec(v___x_3135_);
return v___x_3139_;
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec(v___x_3135_);
v_a_3150_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3137_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3137_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_par___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_3125_ = stack[0].m_obj;
lean_object* v_a_3126_ = stack[1].m_obj;
lean_object* v_a_3127_ = stack[2].m_obj;
lean_object* v_a_3128_ = stack[3].m_obj;
lean_object* v_a_3129_ = stack[4].m_obj;
lean_object* v_a_3130_ = stack[5].m_obj;
lean_object* v_a_3131_ = stack[6].m_obj;
lean_object* v_a_3132_ = stack[7].m_obj;
lean_object* v_a_3133_ = stack[8].m_obj;
lean_object* v_res_3158_;
v_res_3158_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
stack->m_obj
 = v_res_3158_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg___boxed(lean_object* v_jobs_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
return v_res_3169_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_par(lean_object* v_00_u03b1_3170_, lean_object* v_jobs_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_par_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_3171_ = stack[1].m_obj;
lean_object* v_a_3172_ = stack[2].m_obj;
lean_object* v_a_3173_ = stack[3].m_obj;
lean_object* v_a_3174_ = stack[4].m_obj;
lean_object* v_a_3175_ = stack[5].m_obj;
lean_object* v_a_3176_ = stack[6].m_obj;
lean_object* v_a_3177_ = stack[7].m_obj;
lean_object* v_a_3178_ = stack[8].m_obj;
lean_object* v_a_3179_ = stack[9].m_obj;
lean_object* v_res_3182_;
v_res_3182_ = l_Lean_Elab_Tactic_TacticM_par(lean_box(0), v_jobs_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_);
stack->m_obj
 = v_res_3182_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___boxed(lean_object* v_00_u03b1_3183_, lean_object* v_jobs_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_Elab_Tactic_TacticM_par(v_00_u03b1_3183_, v_jobs_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
return v_res_3194_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(lean_object* v_00_u03b1_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3196_, v_x_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3196_ = stack[1].m_obj;
lean_object* v_x_3197_ = stack[2].m_obj;
lean_object* v___y_3198_ = stack[3].m_obj;
lean_object* v___y_3199_ = stack[4].m_obj;
lean_object* v___y_3200_ = stack[5].m_obj;
lean_object* v___y_3201_ = stack[6].m_obj;
lean_object* v___y_3202_ = stack[7].m_obj;
lean_object* v___y_3203_ = stack[8].m_obj;
lean_object* v___y_3204_ = stack[9].m_obj;
lean_object* v___y_3205_ = stack[10].m_obj;
lean_object* v_res_3208_;
v_res_3208_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(lean_box(0), v_x_3196_, v_x_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
stack->m_obj
 = v_res_3208_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___boxed(lean_object* v_00_u03b1_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(v_00_u03b1_3209_, v_x_3210_, v_x_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
return v_res_3221_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(lean_object* v_00_u03b1_3222_, lean_object* v_as_3223_, lean_object* v_as_x27_3224_, lean_object* v_b_3225_, lean_object* v_a_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_3224_, v_b_3225_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
return v___x_3236_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3223_ = stack[1].m_obj;
lean_object* v_as_x27_3224_ = stack[2].m_obj;
lean_object* v_b_3225_ = stack[3].m_obj;
lean_object* v___y_3227_ = stack[5].m_obj;
lean_object* v___y_3228_ = stack[6].m_obj;
lean_object* v___y_3229_ = stack[7].m_obj;
lean_object* v___y_3230_ = stack[8].m_obj;
lean_object* v___y_3231_ = stack[9].m_obj;
lean_object* v___y_3232_ = stack[10].m_obj;
lean_object* v___y_3233_ = stack[11].m_obj;
lean_object* v___y_3234_ = stack[12].m_obj;
lean_object* v_res_3237_;
v_res_3237_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(lean_box(0), v_as_3223_, v_as_x27_3224_, v_b_3225_, lean_box(0), v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
stack->m_obj
 = v_res_3237_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___boxed(lean_object* v_00_u03b1_3238_, lean_object* v_as_3239_, lean_object* v_as_x27_3240_, lean_object* v_b_3241_, lean_object* v_a_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(v_00_u03b1_3238_, v_as_3239_, v_as_x27_3240_, v_b_3241_, v_a_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v_as_x27_3240_);
lean_dec(v_as_3239_);
return v_res_3252_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(lean_object* v_as_x27_3253_, lean_object* v_b_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
if (lean_obj_tag(v_as_x27_3253_) == 0)
{
lean_object* v___x_3264_; 
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v_b_3254_);
return v___x_3264_;
}
else
{
lean_object* v_head_3265_; lean_object* v_tail_3266_; lean_object* v___x_3267_; 
v_head_3265_ = lean_ctor_get(v_as_x27_3253_, 0);
v_tail_3266_ = lean_ctor_get(v_as_x27_3253_, 1);
v___x_3267_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3256_, v___y_3258_, v___y_3260_, v___y_3262_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_2362__overap_3269_; lean_object* v___x_3270_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3267_, 1);
lean_inc(v_head_3265_);
v___x_2362__overap_3269_ = lean_task_get_own(v_head_3265_);
lean_inc(v___y_3262_);
lean_inc_ref(v___y_3261_);
lean_inc(v___y_3260_);
lean_inc_ref(v___y_3259_);
lean_inc(v___y_3258_);
lean_inc_ref(v___y_3257_);
lean_inc(v___y_3256_);
lean_inc_ref(v___y_3255_);
v___x_3270_ = lean_apply_9(v___x_2362__overap_3269_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, lean_box(0));
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
lean_dec(v_a_3268_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v_a_3271_);
v___x_3273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
lean_ctor_set(v___x_3273_, 1, v_b_3254_);
v_as_x27_3253_ = v_tail_3266_;
v_b_3254_ = v___x_3273_;
goto _start;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3298_; 
v_a_3275_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3277_ = v___x_3270_;
v_isShared_3278_ = v_isSharedCheck_3298_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3270_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3298_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
uint8_t v___y_3280_; uint8_t v___x_3296_; 
v___x_3296_ = l_Lean_Exception_isInterrupt(v_a_3275_);
if (v___x_3296_ == 0)
{
uint8_t v___x_3297_; 
lean_inc(v_a_3275_);
v___x_3297_ = l_Lean_Exception_isRuntime(v_a_3275_);
v___y_3280_ = v___x_3297_;
goto v___jp_3279_;
}
else
{
v___y_3280_ = v___x_3296_;
goto v___jp_3279_;
}
v___jp_3279_:
{
if (v___y_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_del_object(v___x_3277_);
v___x_3281_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3268_, v___y_3280_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec_ref_known(v___x_3281_, 1);
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v_a_3275_);
v___x_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v_b_3254_);
v_as_x27_3253_ = v_tail_3266_;
v_b_3254_ = v___x_3283_;
goto _start;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_a_3275_);
lean_dec(v_b_3254_);
v_a_3285_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3281_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3281_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v___x_3294_; 
lean_dec(v_a_3268_);
lean_dec(v_b_3254_);
if (v_isShared_3278_ == 0)
{
v___x_3294_ = v___x_3277_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3275_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_b_3254_);
v_a_3299_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3267_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3267_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_3253_ = stack[0].m_obj;
lean_object* v_b_3254_ = stack[1].m_obj;
lean_object* v___y_3255_ = stack[2].m_obj;
lean_object* v___y_3256_ = stack[3].m_obj;
lean_object* v___y_3257_ = stack[4].m_obj;
lean_object* v___y_3258_ = stack[5].m_obj;
lean_object* v___y_3259_ = stack[6].m_obj;
lean_object* v___y_3260_ = stack[7].m_obj;
lean_object* v___y_3261_ = stack[8].m_obj;
lean_object* v___y_3262_ = stack[9].m_obj;
lean_object* v_res_3307_;
v_res_3307_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_as_x27_3253_, v_b_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
stack->m_obj
 = v_res_3307_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_3308_, lean_object* v_b_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_as_x27_3308_, v_b_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v_as_x27_3308_);
return v_res_3319_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg(lean_object* v_jobs_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3330_ = lean_st_ref_get(v_a_3322_);
v___x_3331_ = lean_box(0);
v___x_3332_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_jobs_3320_, v___x_3331_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v_a_3333_; lean_object* v___x_3334_; 
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
lean_inc(v_a_3333_);
lean_dec_ref_known(v___x_3332_, 1);
v___x_3334_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_a_3333_, v___x_3331_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
lean_dec(v_a_3333_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3344_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3337_ = v___x_3334_;
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3334_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3339_ = lean_st_ref_swap(v_a_3322_, v___x_3330_);
lean_dec(v___x_3339_);
v___x_3340_ = l_List_reverse___redArg(v_a_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 0, v___x_3340_);
v___x_3342_ = v___x_3337_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
else
{
lean_dec(v___x_3330_);
return v___x_3334_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v___x_3330_);
v_a_3345_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3332_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3332_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_par_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_3320_ = stack[0].m_obj;
lean_object* v_a_3321_ = stack[1].m_obj;
lean_object* v_a_3322_ = stack[2].m_obj;
lean_object* v_a_3323_ = stack[3].m_obj;
lean_object* v_a_3324_ = stack[4].m_obj;
lean_object* v_a_3325_ = stack[5].m_obj;
lean_object* v_a_3326_ = stack[6].m_obj;
lean_object* v_a_3327_ = stack[7].m_obj;
lean_object* v_a_3328_ = stack[8].m_obj;
lean_object* v_res_3353_;
v_res_3353_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(v_jobs_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
stack->m_obj
 = v_res_3353_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg___boxed(lean_object* v_jobs_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(v_jobs_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
return v_res_3364_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_par_x27(lean_object* v_00_u03b1_3365_, lean_object* v_jobs_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(v_jobs_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
return v___x_3376_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_par_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_3366_ = stack[1].m_obj;
lean_object* v_a_3367_ = stack[2].m_obj;
lean_object* v_a_3368_ = stack[3].m_obj;
lean_object* v_a_3369_ = stack[4].m_obj;
lean_object* v_a_3370_ = stack[5].m_obj;
lean_object* v_a_3371_ = stack[6].m_obj;
lean_object* v_a_3372_ = stack[7].m_obj;
lean_object* v_a_3373_ = stack[8].m_obj;
lean_object* v_a_3374_ = stack[9].m_obj;
lean_object* v_res_3377_;
v_res_3377_ = l_Lean_Elab_Tactic_TacticM_par_x27(lean_box(0), v_jobs_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_);
stack->m_obj
 = v_res_3377_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___boxed(lean_object* v_00_u03b1_3378_, lean_object* v_jobs_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_Elab_Tactic_TacticM_par_x27(v_00_u03b1_3378_, v_jobs_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec(v_a_3385_);
lean_dec_ref(v_a_3384_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
return v_res_3389_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(lean_object* v_00_u03b1_3390_, lean_object* v_as_3391_, lean_object* v_as_x27_3392_, lean_object* v_b_3393_, lean_object* v_a_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_as_x27_3392_, v_b_3393_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3404_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3391_ = stack[1].m_obj;
lean_object* v_as_x27_3392_ = stack[2].m_obj;
lean_object* v_b_3393_ = stack[3].m_obj;
lean_object* v___y_3395_ = stack[5].m_obj;
lean_object* v___y_3396_ = stack[6].m_obj;
lean_object* v___y_3397_ = stack[7].m_obj;
lean_object* v___y_3398_ = stack[8].m_obj;
lean_object* v___y_3399_ = stack[9].m_obj;
lean_object* v___y_3400_ = stack[10].m_obj;
lean_object* v___y_3401_ = stack[11].m_obj;
lean_object* v___y_3402_ = stack[12].m_obj;
lean_object* v_res_3405_;
v_res_3405_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(lean_box(0), v_as_3391_, v_as_x27_3392_, v_b_3393_, lean_box(0), v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
stack->m_obj
 = v_res_3405_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_3406_, lean_object* v_as_3407_, lean_object* v_as_x27_3408_, lean_object* v_b_3409_, lean_object* v_a_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(v_00_u03b1_3406_, v_as_3407_, v_as_x27_3408_, v_b_3409_, v_a_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v_as_x27_3408_);
lean_dec(v_as_3407_);
return v_res_3420_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_3421_, lean_object* v___x_3422_, lean_object* v_____r_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3433_, 0, v_a_3421_);
v___x_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3422_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3434_);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3421_ = stack[0].m_obj;
lean_object* v___x_3422_ = stack[1].m_obj;
lean_object* v_____r_3423_ = stack[2].m_obj;
lean_object* v___y_3424_ = stack[3].m_obj;
lean_object* v___y_3425_ = stack[4].m_obj;
lean_object* v___y_3426_ = stack[5].m_obj;
lean_object* v___y_3427_ = stack[6].m_obj;
lean_object* v___y_3428_ = stack[7].m_obj;
lean_object* v___y_3429_ = stack[8].m_obj;
lean_object* v___y_3430_ = stack[9].m_obj;
lean_object* v___y_3431_ = stack[10].m_obj;
lean_object* v_res_3437_;
v_res_3437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3421_, v___x_3422_, v_____r_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
stack->m_obj
 = v_res_3437_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_3438_, lean_object* v___x_3439_, lean_object* v_____r_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3438_, v___x_3439_, v_____r_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3450_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(uint8_t v_cancel_3451_, lean_object* v_fst_3452_, lean_object* v_a_3453_, lean_object* v_b_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_){
_start:
{
if (lean_obj_tag(v_a_3453_) == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref(v_fst_3452_);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v_b_3454_);
return v___x_3464_;
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v_fst_3468_; lean_object* v_snd_3469_; lean_object* v___y_3471_; lean_object* v___x_3491_; 
lean_dec_ref(v_b_3454_);
v___x_3465_ = lean_box(0);
v___x_3466_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_3467_ = l_IO_waitAny_x27___redArg(v_a_3453_);
v_fst_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_fst_3468_);
v_snd_3469_ = lean_ctor_get(v___x_3467_, 1);
lean_inc(v_snd_3469_);
lean_dec_ref(v___x_3467_);
v___x_3491_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3456_, v___y_3458_, v___y_3460_, v___y_3462_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
lean_inc(v___y_3462_);
lean_inc_ref(v___y_3461_);
lean_inc(v___y_3460_);
lean_inc_ref(v___y_3459_);
lean_inc(v___y_3458_);
lean_inc_ref(v___y_3457_);
lean_inc(v___y_3456_);
lean_inc_ref(v___y_3455_);
v___x_3493_ = lean_apply_9(v_fst_3468_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, lean_box(0));
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_dec(v_a_3492_);
if (v_cancel_3451_ == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3494_, v___x_3465_, v___x_3465_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
v___y_3471_ = v___x_3495_;
goto v___jp_3470_;
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_a_3496_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3493_, 1);
lean_inc_ref(v_fst_3452_);
v___x_3497_ = lean_apply_1(v_fst_3452_, lean_box(0));
v___x_3498_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3496_, v___x_3465_, v___x_3497_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
v___y_3471_ = v___x_3498_;
goto v___jp_3470_;
}
}
else
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3520_; 
v_a_3499_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3501_ = v___x_3493_;
v_isShared_3502_ = v_isSharedCheck_3520_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3493_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3520_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
uint8_t v___y_3504_; uint8_t v___x_3518_; 
v___x_3518_ = l_Lean_Exception_isInterrupt(v_a_3499_);
if (v___x_3518_ == 0)
{
uint8_t v___x_3519_; 
lean_inc(v_a_3499_);
v___x_3519_ = l_Lean_Exception_isRuntime(v_a_3499_);
v___y_3504_ = v___x_3519_;
goto v___jp_3503_;
}
else
{
v___y_3504_ = v___x_3518_;
goto v___jp_3503_;
}
v___jp_3503_:
{
if (v___y_3504_ == 0)
{
lean_object* v___x_3505_; 
lean_del_object(v___x_3501_);
lean_dec(v_a_3499_);
v___x_3505_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3492_, v___y_3504_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_dec_ref_known(v___x_3505_, 1);
v_a_3453_ = v_snd_3469_;
v_b_3454_ = v___x_3466_;
goto _start;
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec(v_snd_3469_);
lean_dec_ref(v_fst_3452_);
v_a_3507_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3505_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3505_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
else
{
lean_object* v___x_3516_; 
lean_dec(v_a_3492_);
lean_dec(v_snd_3469_);
lean_dec_ref(v_fst_3452_);
if (v_isShared_3502_ == 0)
{
v___x_3516_ = v___x_3501_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3499_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_snd_3469_);
lean_dec(v_fst_3468_);
lean_dec_ref(v_fst_3452_);
v_a_3521_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3491_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3491_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
v___jp_3470_:
{
if (lean_obj_tag(v___y_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3482_; 
v_a_3472_ = lean_ctor_get(v___y_3471_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___y_3471_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3474_ = v___y_3471_;
v_isShared_3475_ = v_isSharedCheck_3482_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___y_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3482_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
if (lean_obj_tag(v_a_3472_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3478_; 
lean_dec(v_snd_3469_);
lean_dec_ref(v_fst_3452_);
v_a_3476_ = lean_ctor_get(v_a_3472_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v_a_3472_, 1);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v_a_3476_);
v___x_3478_ = v___x_3474_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3476_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
else
{
lean_object* v_a_3480_; 
lean_del_object(v___x_3474_);
v_a_3480_ = lean_ctor_get(v_a_3472_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v_a_3472_, 1);
v_a_3453_ = v_snd_3469_;
v_b_3454_ = v_a_3480_;
goto _start;
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec(v_snd_3469_);
lean_dec_ref(v_fst_3452_);
v_a_3483_ = lean_ctor_get(v___y_3471_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___y_3471_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___y_3471_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___y_3471_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_3451_ = stack[0].m_num;
lean_object* v_fst_3452_ = stack[1].m_obj;
lean_object* v_a_3453_ = stack[2].m_obj;
lean_object* v_b_3454_ = stack[3].m_obj;
lean_object* v___y_3455_ = stack[4].m_obj;
lean_object* v___y_3456_ = stack[5].m_obj;
lean_object* v___y_3457_ = stack[6].m_obj;
lean_object* v___y_3458_ = stack[7].m_obj;
lean_object* v___y_3459_ = stack[8].m_obj;
lean_object* v___y_3460_ = stack[9].m_obj;
lean_object* v___y_3461_ = stack[10].m_obj;
lean_object* v___y_3462_ = stack[11].m_obj;
lean_object* v_res_3529_;
v_res_3529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3451_, v_fst_3452_, v_a_3453_, v_b_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
stack->m_obj
 = v_res_3529_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_3530_, lean_object* v_fst_3531_, lean_object* v_a_3532_, lean_object* v_b_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
uint8_t v_cancel_boxed_3543_; lean_object* v_res_3544_; 
v_cancel_boxed_3543_ = lean_unbox(v_cancel_3530_);
v_res_3544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_boxed_3543_, v_fst_3531_, v_a_3532_, v_b_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3544_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(lean_object* v_msg_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_ref_3551_; lean_object* v___x_3552_; lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3561_; 
v_ref_3551_ = lean_ctor_get(v___y_3548_, 2);
v___x_3552_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3561_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3557_; lean_object* v___x_3559_; 
lean_inc(v_ref_3551_);
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_ref_3551_);
lean_ctor_set(v___x_3557_, 1, v_a_3553_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set_tag(v___x_3555_, 1);
lean_ctor_set(v___x_3555_, 0, v___x_3557_);
v___x_3559_ = v___x_3555_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3545_ = stack[0].m_obj;
lean_object* v___y_3546_ = stack[1].m_obj;
lean_object* v___y_3547_ = stack[2].m_obj;
lean_object* v___y_3548_ = stack[3].m_obj;
lean_object* v___y_3549_ = stack[4].m_obj;
lean_object* v_res_3562_;
v_res_3562_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
stack->m_obj
 = v_res_3562_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3563_, v___y_3564_, v___y_3565_, v___y_3566_, v___y_3567_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
return v_res_3569_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg(lean_object* v_jobs_3570_, uint8_t v_cancel_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_3570_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v_fst_3583_; lean_object* v_snd_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v_fst_3583_ = lean_ctor_get(v_a_3582_, 0);
lean_inc(v_fst_3583_);
v_snd_3584_ = lean_ctor_get(v_a_3582_, 1);
lean_inc(v_snd_3584_);
lean_dec(v_a_3582_);
v___x_3585_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_3586_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3571_, v_fst_3583_, v_snd_3584_, v___x_3585_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3598_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3598_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3598_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v_fst_3591_; 
v_fst_3591_ = lean_ctor_get(v_a_3587_, 0);
lean_inc(v_fst_3591_);
lean_dec(v_a_3587_);
if (lean_obj_tag(v_fst_3591_) == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_del_object(v___x_3589_);
v___x_3592_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_3593_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v___x_3592_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
return v___x_3593_;
}
else
{
lean_object* v_val_3594_; lean_object* v___x_3596_; 
v_val_3594_ = lean_ctor_get(v_fst_3591_, 0);
lean_inc(v_val_3594_);
lean_dec_ref_known(v_fst_3591_, 1);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v_val_3594_);
v___x_3596_ = v___x_3589_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_val_3594_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
v_a_3599_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3586_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3586_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
v_a_3607_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3581_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3581_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parFirst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_3570_ = stack[0].m_obj;
uint8_t v_cancel_3571_ = stack[1].m_num;
lean_object* v_a_3572_ = stack[2].m_obj;
lean_object* v_a_3573_ = stack[3].m_obj;
lean_object* v_a_3574_ = stack[4].m_obj;
lean_object* v_a_3575_ = stack[5].m_obj;
lean_object* v_a_3576_ = stack[6].m_obj;
lean_object* v_a_3577_ = stack[7].m_obj;
lean_object* v_a_3578_ = stack[8].m_obj;
lean_object* v_a_3579_ = stack[9].m_obj;
lean_object* v_res_3615_;
v_res_3615_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3570_, v_cancel_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
stack->m_obj
 = v_res_3615_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg___boxed(lean_object* v_jobs_3616_, lean_object* v_cancel_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
uint8_t v_cancel_boxed_3627_; lean_object* v_res_3628_; 
v_cancel_boxed_3627_ = lean_unbox(v_cancel_3617_);
v_res_3628_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3616_, v_cancel_boxed_3627_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_);
lean_dec(v_a_3625_);
lean_dec_ref(v_a_3624_);
lean_dec(v_a_3623_);
lean_dec_ref(v_a_3622_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
return v_res_3628_;
}
}
lean_object* l_Lean_Elab_Tactic_TacticM_parFirst(lean_object* v_00_u03b1_3629_, lean_object* v_jobs_3630_, uint8_t v_cancel_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3630_, v_cancel_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_TacticM_parFirst_0interp(lean_interpreter_value* stack)
{
lean_object* v_jobs_3630_ = stack[1].m_obj;
uint8_t v_cancel_3631_ = stack[2].m_num;
lean_object* v_a_3632_ = stack[3].m_obj;
lean_object* v_a_3633_ = stack[4].m_obj;
lean_object* v_a_3634_ = stack[5].m_obj;
lean_object* v_a_3635_ = stack[6].m_obj;
lean_object* v_a_3636_ = stack[7].m_obj;
lean_object* v_a_3637_ = stack[8].m_obj;
lean_object* v_a_3638_ = stack[9].m_obj;
lean_object* v_a_3639_ = stack[10].m_obj;
lean_object* v_res_3642_;
v_res_3642_ = l_Lean_Elab_Tactic_TacticM_parFirst(lean_box(0), v_jobs_3630_, v_cancel_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
stack->m_obj
 = v_res_3642_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_jobs_3644_, lean_object* v_cancel_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
uint8_t v_cancel_boxed_3655_; lean_object* v_res_3656_; 
v_cancel_boxed_3655_ = lean_unbox(v_cancel_3645_);
v_res_3656_ = l_Lean_Elab_Tactic_TacticM_parFirst(v_00_u03b1_3643_, v_jobs_3644_, v_cancel_boxed_3655_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
lean_dec(v_a_3651_);
lean_dec_ref(v_a_3650_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3656_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(lean_object* v_00_u03b1_3657_, uint8_t v_cancel_3658_, lean_object* v_fst_3659_, lean_object* v_inst_3660_, lean_object* v_R_3661_, lean_object* v_a_3662_, lean_object* v_b_3663_, lean_object* v_c_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3658_, v_fst_3659_, v_a_3662_, v_b_3663_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
return v___x_3674_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_cancel_3658_ = stack[1].m_num;
lean_object* v_fst_3659_ = stack[2].m_obj;
lean_object* v_a_3662_ = stack[5].m_obj;
lean_object* v_b_3663_ = stack[6].m_obj;
lean_object* v___y_3665_ = stack[8].m_obj;
lean_object* v___y_3666_ = stack[9].m_obj;
lean_object* v___y_3667_ = stack[10].m_obj;
lean_object* v___y_3668_ = stack[11].m_obj;
lean_object* v___y_3669_ = stack[12].m_obj;
lean_object* v___y_3670_ = stack[13].m_obj;
lean_object* v___y_3671_ = stack[14].m_obj;
lean_object* v___y_3672_ = stack[15].m_obj;
lean_object* v_res_3675_;
v_res_3675_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(lean_box(0), v_cancel_3658_, v_fst_3659_, lean_box(0), lean_box(0), v_a_3662_, v_b_3663_, lean_box(0), v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
stack->m_obj
 = v_res_3675_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_3676_ = _args[0];
lean_object* v_cancel_3677_ = _args[1];
lean_object* v_fst_3678_ = _args[2];
lean_object* v_inst_3679_ = _args[3];
lean_object* v_R_3680_ = _args[4];
lean_object* v_a_3681_ = _args[5];
lean_object* v_b_3682_ = _args[6];
lean_object* v_c_3683_ = _args[7];
lean_object* v___y_3684_ = _args[8];
lean_object* v___y_3685_ = _args[9];
lean_object* v___y_3686_ = _args[10];
lean_object* v___y_3687_ = _args[11];
lean_object* v___y_3688_ = _args[12];
lean_object* v___y_3689_ = _args[13];
lean_object* v___y_3690_ = _args[14];
lean_object* v___y_3691_ = _args[15];
lean_object* v___y_3692_ = _args[16];
_start:
{
uint8_t v_cancel_boxed_3693_; lean_object* v_res_3694_; 
v_cancel_boxed_3693_ = lean_unbox(v_cancel_3677_);
v_res_3694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(v_00_u03b1_3676_, v_cancel_boxed_3693_, v_fst_3678_, v_inst_3679_, v_R_3680_, v_a_3681_, v_b_3682_, v_c_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3694_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(lean_object* v_00_u03b1_3695_, lean_object* v_msg_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3696_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3706_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3696_ = stack[1].m_obj;
lean_object* v___y_3697_ = stack[2].m_obj;
lean_object* v___y_3698_ = stack[3].m_obj;
lean_object* v___y_3699_ = stack[4].m_obj;
lean_object* v___y_3700_ = stack[5].m_obj;
lean_object* v___y_3701_ = stack[6].m_obj;
lean_object* v___y_3702_ = stack[7].m_obj;
lean_object* v___y_3703_ = stack[8].m_obj;
lean_object* v___y_3704_ = stack[9].m_obj;
lean_object* v_res_3707_;
v_res_3707_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(lean_box(0), v_msg_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
stack->m_obj
 = v_res_3707_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_3708_, lean_object* v_msg_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(v_00_u03b1_3708_, v_msg_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
return v_res_3719_;
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
