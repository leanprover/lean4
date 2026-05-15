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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_CoreM_asTask_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0 = (const lean_object*)&l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0(lean_object* v_it_1_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0___boxed(lean_object* v_it_14_, lean_object* v___y_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___lam__0(v_it_14_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO(lean_object* v_00_u03b1_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = ((lean_object*)(l___private_Lean_Elab_Parallel_0__Std_Iterators_Types_instIteratorTaskIteratorBaseIO___closed__0));
return v___f_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(lean_object* v_tasks_20_){
_start:
{
lean_inc(v_tasks_20_);
return v_tasks_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg___boxed(lean_object* v_tasks_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks___redArg(v_tasks_21_);
lean_dec(v_tasks_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks(lean_object* v_00_u03b1_23_, lean_object* v_tasks_24_){
_start:
{
lean_inc(v_tasks_24_);
return v_tasks_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Parallel_0__IO_iterTasks___boxed(lean_object* v_00_u03b1_25_, lean_object* v_tasks_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lean_Elab_Parallel_0__IO_iterTasks(v_00_u03b1_25_, v_tasks_26_);
lean_dec(v_tasks_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(lean_object* v_x_28_, lean_object* v_x_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
if (lean_obj_tag(v_x_28_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = l_List_reverse___redArg(v_x_29_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_head_35_; lean_object* v_tail_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_54_; 
v_head_35_ = lean_ctor_get(v_x_28_, 0);
v_tail_36_ = lean_ctor_get(v_x_28_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_28_);
if (v_isSharedCheck_54_ == 0)
{
v___x_38_ = v_x_28_;
v_isShared_39_ = v_isSharedCheck_54_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_tail_36_);
lean_inc(v_head_35_);
lean_dec(v_x_28_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_54_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Core_CoreM_asTask___redArg(v_head_35_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_a_41_);
lean_dec_ref(v___x_40_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 1, v_x_29_);
lean_ctor_set(v___x_38_, 0, v_a_41_);
v___x_43_ = v___x_38_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_41_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_x_29_);
v___x_43_ = v_reuseFailAlloc_45_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
v_x_28_ = v_tail_36_;
v_x_29_ = v___x_43_;
goto _start;
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
lean_del_object(v___x_38_);
lean_dec(v_tail_36_);
lean_dec(v_x_29_);
v_a_46_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_40_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_40_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_x_55_, v_x_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(lean_object* v_as_61_){
_start:
{
if (lean_obj_tag(v_as_61_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v___x_66_; 
v_head_64_ = lean_ctor_get(v_as_61_, 0);
lean_inc(v_head_64_);
v_tail_65_ = lean_ctor_get(v_as_61_, 1);
lean_inc(v_tail_65_);
lean_dec_ref(v_as_61_);
v___x_66_ = lean_apply_1(v_head_64_, lean_box(0));
v_as_61_ = v_tail_65_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed(lean_object* v_as_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1(v_as_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg(lean_object* v_jobs_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_box(0);
v___x_76_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_jobs_71_, v___x_75_, v_a_72_, v_a_73_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_95_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_95_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_95_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_95_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v_fst_82_; lean_object* v_snd_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_94_; 
v___x_81_ = l_List_unzipTR___redArg(v_a_77_);
v_fst_82_ = lean_ctor_get(v___x_81_, 0);
v_snd_83_ = lean_ctor_get(v___x_81_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_94_ == 0)
{
v___x_85_ = v___x_81_;
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_snd_83_);
lean_inc(v_fst_82_);
lean_dec(v___x_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_94_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_87_, 0, v_fst_82_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_snd_83_);
v___x_89_ = v_reuseFailAlloc_93_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_91_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_89_);
v___x_91_ = v___x_79_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_76_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_76_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_104_, v_a_105_, v_a_106_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel(lean_object* v_00_u03b1_109_, lean_object* v_jobs_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_110_, v_a_111_, v_a_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterWithCancel___boxed(lean_object* v_00_u03b1_115_, lean_object* v_jobs_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Core_CoreM_parIterWithCancel(v_00_u03b1_115_, v_jobs_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_121_, lean_object* v_x_122_, lean_object* v_x_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_x_122_, v_x_123_, v___y_124_, v___y_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_128_, lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0(v_00_u03b1_128_, v_x_129_, v_x_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___redArg(lean_object* v_jobs_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Core_CoreM_parIterWithCancel___redArg(v_jobs_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_148_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_148_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_148_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_snd_144_; lean_object* v___x_146_; 
v_snd_144_ = lean_ctor_get(v_a_140_, 1);
lean_inc(v_snd_144_);
lean_dec(v_a_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v_snd_144_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_snd_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_a_149_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_139_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_139_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___redArg___boxed(lean_object* v_jobs_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_157_, v_a_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter(lean_object* v_00_u03b1_162_, lean_object* v_jobs_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Core_CoreM_parIter___redArg(v_jobs_163_, v_a_164_, v_a_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIter___boxed(lean_object* v_00_u03b1_168_, lean_object* v_jobs_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Core_CoreM_parIter(v_00_u03b1_168_, v_jobs_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_box(0);
v___x_179_ = l_List_mapM_loop___at___00Lean_Core_CoreM_parIterWithCancel_spec__0___redArg(v_jobs_174_, v___x_178_, v_a_175_, v_a_176_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_198_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_198_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_198_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_198_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_197_; 
v___x_184_ = l_List_unzipTR___redArg(v_a_180_);
v_fst_185_ = lean_ctor_get(v___x_184_, 0);
v_snd_186_ = lean_ctor_get(v___x_184_, 1);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_197_ == 0)
{
v___x_188_ = v___x_184_;
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
lean_dec(v___x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_197_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_190_, 0, v_fst_185_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_snd_186_);
v___x_192_ = v_reuseFailAlloc_196_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
lean_object* v___x_194_; 
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_192_);
v___x_194_ = v___x_182_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_179_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_179_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel(lean_object* v_00_u03b1_212_, lean_object* v_jobs_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_213_, v_a_214_, v_a_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_218_, lean_object* v_jobs_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Core_CoreM_parIterGreedyWithCancel(v_00_u03b1_218_, v_jobs_219_, v_a_220_, v_a_221_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg(lean_object* v_jobs_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_237_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_237_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_237_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_snd_233_; lean_object* v___x_235_; 
v_snd_233_ = lean_ctor_get(v_a_229_, 1);
lean_inc(v_snd_233_);
lean_dec(v_a_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v_snd_233_);
v___x_235_ = v___x_231_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_snd_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
v_a_238_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_228_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_228_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___redArg___boxed(lean_object* v_jobs_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy(lean_object* v_00_u03b1_251_, lean_object* v_jobs_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Core_CoreM_parIterGreedy___redArg(v_jobs_252_, v_a_253_, v_a_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parIterGreedy___boxed(lean_object* v_00_u03b1_257_, lean_object* v_jobs_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Core_CoreM_parIterGreedy(v_00_u03b1_257_, v_jobs_258_, v_a_259_, v_a_260_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(lean_object* v_as_x27_263_, lean_object* v_b_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
if (lean_obj_tag(v_as_x27_263_) == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v_b_264_);
return v___x_268_;
}
else
{
lean_object* v_head_269_; lean_object* v_tail_270_; lean_object* v_a_272_; lean_object* v___y_276_; uint8_t v___y_277_; lean_object* v_a_281_; lean_object* v___x_1781__overap_284_; lean_object* v___x_285_; 
v_head_269_ = lean_ctor_get(v_as_x27_263_, 0);
v_tail_270_ = lean_ctor_get(v_as_x27_263_, 1);
lean_inc(v_head_269_);
v___x_1781__overap_284_ = lean_task_get_own(v_head_269_);
lean_inc(v___y_266_);
lean_inc_ref(v___y_265_);
v___x_285_ = lean_apply_3(v___x_1781__overap_284_, v___y_265_, v___y_266_, lean_box(0));
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref(v___x_285_);
v___x_287_ = l_Lean_Core_saveState___redArg(v___y_266_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_a_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_296_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_a_286_);
lean_ctor_set(v___x_292_, 1, v_a_288_);
if (v_isShared_291_ == 0)
{
lean_ctor_set_tag(v___x_290_, 1);
lean_ctor_set(v___x_290_, 0, v___x_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
v_a_272_ = v___x_294_;
goto v___jp_271_;
}
}
}
else
{
lean_object* v_a_297_; 
lean_dec(v_a_286_);
v_a_297_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_a_297_);
lean_dec_ref(v___x_287_);
v_a_281_ = v_a_297_;
goto v___jp_280_;
}
}
else
{
lean_object* v_a_298_; 
v_a_298_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_298_);
lean_dec_ref(v___x_285_);
v_a_281_ = v_a_298_;
goto v___jp_280_;
}
v___jp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v_a_272_);
lean_ctor_set(v___x_273_, 1, v_b_264_);
v_as_x27_263_ = v_tail_270_;
v_b_264_ = v___x_273_;
goto _start;
}
v___jp_275_:
{
if (v___y_277_ == 0)
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___y_276_);
v_a_272_ = v___x_278_;
goto v___jp_271_;
}
else
{
lean_object* v___x_279_; 
lean_dec(v_b_264_);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v___y_276_);
return v___x_279_;
}
}
v___jp_280_:
{
uint8_t v___x_282_; 
v___x_282_ = l_Lean_Exception_isInterrupt(v_a_281_);
if (v___x_282_ == 0)
{
uint8_t v___x_283_; 
lean_inc_ref(v_a_281_);
v___x_283_ = l_Lean_Exception_isRuntime(v_a_281_);
v___y_276_ = v_a_281_;
v___y_277_ = v___x_283_;
goto v___jp_275_;
}
else
{
v___y_276_ = v_a_281_;
v___y_277_ = v___x_282_;
goto v___jp_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg___boxed(lean_object* v_as_x27_299_, lean_object* v_b_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_299_, v_b_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v_as_x27_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = l_List_reverse___redArg(v_x_306_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
else
{
lean_object* v_head_312_; lean_object* v_tail_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_331_; 
v_head_312_ = lean_ctor_get(v_x_305_, 0);
v_tail_313_ = lean_ctor_get(v_x_305_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_331_ == 0)
{
v___x_315_ = v_x_305_;
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_tail_313_);
lean_inc(v_head_312_);
lean_dec(v_x_305_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Core_CoreM_asTask_x27___redArg(v_head_312_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref(v___x_317_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v_x_306_);
lean_ctor_set(v___x_315_, 0, v_a_318_);
v___x_320_ = v___x_315_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_318_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_x_306_);
v___x_320_ = v_reuseFailAlloc_322_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
v_x_305_ = v_tail_313_;
v_x_306_ = v___x_320_;
goto _start;
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_del_object(v___x_315_);
lean_dec(v_tail_313_);
lean_dec(v_x_306_);
v_a_323_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_317_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_317_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg___boxed(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_332_, v_x_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg(lean_object* v_jobs_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_st_ref_get(v_a_340_);
v___x_343_ = lean_box(0);
v___x_344_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_338_, v___x_343_, v_a_339_, v_a_340_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_346_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref(v___x_344_);
v___x_346_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_a_345_, v___x_343_, v_a_339_, v_a_340_);
lean_dec(v_a_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_356_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_356_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_356_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_356_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = lean_st_ref_set(v_a_340_, v___x_342_);
v___x_352_ = l_List_reverse___redArg(v_a_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_352_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
else
{
lean_dec(v___x_342_);
return v___x_346_;
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v___x_342_);
v_a_357_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_344_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_344_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___redArg___boxed(lean_object* v_jobs_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Core_CoreM_par___redArg(v_jobs_365_, v_a_366_, v_a_367_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par(lean_object* v_00_u03b1_370_, lean_object* v_jobs_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Core_CoreM_par___redArg(v_jobs_371_, v_a_372_, v_a_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par___boxed(lean_object* v_00_u03b1_376_, lean_object* v_jobs_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Core_CoreM_par(v_00_u03b1_376_, v_jobs_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(lean_object* v_00_u03b1_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_x_383_, v_x_384_, v___y_385_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___boxed(lean_object* v_00_u03b1_389_, lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0(v_00_u03b1_389_, v_x_390_, v_x_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(lean_object* v_00_u03b1_396_, lean_object* v_as_397_, lean_object* v_as_x27_398_, lean_object* v_b_399_, lean_object* v_a_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___redArg(v_as_x27_398_, v_b_399_, v___y_401_, v___y_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1___boxed(lean_object* v_00_u03b1_405_, lean_object* v_as_406_, lean_object* v_as_x27_407_, lean_object* v_b_408_, lean_object* v_a_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_spec__1(v_00_u03b1_405_, v_as_406_, v_as_x27_407_, v_b_408_, v_a_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v_as_x27_407_);
lean_dec(v_as_406_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(lean_object* v_as_x27_414_, lean_object* v_b_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
if (lean_obj_tag(v_as_x27_414_) == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_b_415_);
return v___x_419_;
}
else
{
lean_object* v_head_420_; lean_object* v_tail_421_; lean_object* v___x_1591__overap_422_; lean_object* v___x_423_; 
v_head_420_ = lean_ctor_get(v_as_x27_414_, 0);
v_tail_421_ = lean_ctor_get(v_as_x27_414_, 1);
lean_inc(v_head_420_);
v___x_1591__overap_422_ = lean_task_get_own(v_head_420_);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
v___x_423_ = lean_apply_3(v___x_1591__overap_422_, v___y_416_, v___y_417_, lean_box(0));
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref(v___x_423_);
v___x_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_425_, 0, v_a_424_);
v___x_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_b_415_);
v_as_x27_414_ = v_tail_421_;
v_b_415_ = v___x_426_;
goto _start;
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_442_; 
v_a_428_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_442_ == 0)
{
v___x_430_ = v___x_423_;
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_423_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___y_433_; uint8_t v___x_440_; 
v___x_440_ = l_Lean_Exception_isInterrupt(v_a_428_);
if (v___x_440_ == 0)
{
uint8_t v___x_441_; 
lean_inc(v_a_428_);
v___x_441_ = l_Lean_Exception_isRuntime(v_a_428_);
v___y_433_ = v___x_441_;
goto v___jp_432_;
}
else
{
v___y_433_ = v___x_440_;
goto v___jp_432_;
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_del_object(v___x_430_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v_a_428_);
v___x_435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_b_415_);
v_as_x27_414_ = v_tail_421_;
v_b_415_ = v___x_435_;
goto _start;
}
else
{
lean_object* v___x_438_; 
lean_dec(v_b_415_);
if (v_isShared_431_ == 0)
{
v___x_438_ = v___x_430_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_a_428_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_443_, v_b_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v_as_x27_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg(lean_object* v_jobs_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_st_ref_get(v_a_451_);
v___x_454_ = lean_box(0);
v___x_455_ = l_List_mapM_loop___at___00Lean_Core_CoreM_par_spec__0___redArg(v_jobs_449_, v___x_454_, v_a_450_, v_a_451_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref(v___x_455_);
v___x_457_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_a_456_, v___x_454_, v_a_450_, v_a_451_);
lean_dec(v_a_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_467_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_467_ == 0)
{
v___x_460_ = v___x_457_;
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_457_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_467_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_462_ = lean_st_ref_set(v_a_451_, v___x_453_);
v___x_463_ = l_List_reverse___redArg(v_a_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 0, v___x_463_);
v___x_465_ = v___x_460_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
else
{
lean_dec(v___x_453_);
return v___x_457_;
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_dec(v___x_453_);
v_a_468_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_455_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_455_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___redArg___boxed(lean_object* v_jobs_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27(lean_object* v_00_u03b1_481_, lean_object* v_jobs_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Core_CoreM_par_x27___redArg(v_jobs_482_, v_a_483_, v_a_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_par_x27___boxed(lean_object* v_00_u03b1_487_, lean_object* v_jobs_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Core_CoreM_par_x27(v_00_u03b1_487_, v_jobs_488_, v_a_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(lean_object* v_00_u03b1_493_, lean_object* v_as_494_, lean_object* v_as_x27_495_, lean_object* v_b_496_, lean_object* v_a_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___redArg(v_as_x27_495_, v_b_496_, v___y_498_, v___y_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_502_, lean_object* v_as_503_, lean_object* v_as_x27_504_, lean_object* v_b_505_, lean_object* v_a_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_List_forIn_x27_loop___at___00Lean_Core_CoreM_par_x27_spec__0(v_00_u03b1_502_, v_as_503_, v_as_x27_504_, v_b_505_, v_a_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v_as_x27_504_);
lean_dec(v_as_503_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_511_, lean_object* v___x_512_, lean_object* v_____r_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v_a_511_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_512_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_521_, lean_object* v___x_522_, lean_object* v_____r_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_521_, v___x_522_, v_____r_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(uint8_t v_cancel_531_, lean_object* v_fst_532_, lean_object* v_a_533_, lean_object* v_b_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
if (lean_obj_tag(v_a_533_) == 0)
{
lean_object* v___x_538_; 
lean_dec_ref(v_fst_532_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_b_534_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___y_543_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec_ref(v_b_534_);
v___x_539_ = l_IO_waitAny_x27___redArg(v_a_533_);
v_fst_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_fst_540_);
v_snd_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc(v_snd_541_);
lean_dec_ref(v___x_539_);
v___x_563_ = lean_box(0);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
v___x_564_ = lean_apply_3(v_fst_540_, v___y_535_, v___y_536_, lean_box(0));
if (lean_obj_tag(v___x_564_) == 0)
{
if (v_cancel_531_ == 0)
{
lean_object* v_a_565_; lean_object* v___x_566_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref(v___x_564_);
v___x_566_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_565_, v___x_563_, v___x_563_, v___y_535_, v___y_536_);
v___y_543_ = v___x_566_;
goto v___jp_542_;
}
else
{
lean_object* v_a_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_a_567_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_567_);
lean_dec_ref(v___x_564_);
lean_inc_ref(v_fst_532_);
v___x_568_ = lean_apply_1(v_fst_532_, lean_box(0));
v___x_569_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___lam__0(v_a_567_, v___x_563_, v___x_568_, v___y_535_, v___y_536_);
v___y_543_ = v___x_569_;
goto v___jp_542_;
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_583_; 
v_a_570_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_583_ == 0)
{
v___x_572_ = v___x_564_;
v_isShared_573_ = v_isSharedCheck_583_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_564_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_583_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; uint8_t v___y_576_; uint8_t v___x_581_; 
v___x_574_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_581_ = l_Lean_Exception_isInterrupt(v_a_570_);
if (v___x_581_ == 0)
{
uint8_t v___x_582_; 
lean_inc(v_a_570_);
v___x_582_ = l_Lean_Exception_isRuntime(v_a_570_);
v___y_576_ = v___x_582_;
goto v___jp_575_;
}
else
{
v___y_576_ = v___x_581_;
goto v___jp_575_;
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
lean_del_object(v___x_572_);
lean_dec(v_a_570_);
v_a_533_ = v_snd_541_;
v_b_534_ = v___x_574_;
goto _start;
}
else
{
lean_object* v___x_579_; 
lean_dec(v_snd_541_);
lean_dec_ref(v_fst_532_);
if (v_isShared_573_ == 0)
{
v___x_579_ = v___x_572_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_570_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
v___jp_542_:
{
if (lean_obj_tag(v___y_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_554_; 
v_a_544_ = lean_ctor_get(v___y_543_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___y_543_);
if (v_isSharedCheck_554_ == 0)
{
v___x_546_ = v___y_543_;
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___y_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_554_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
if (lean_obj_tag(v_a_544_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_550_; 
lean_dec(v_snd_541_);
lean_dec_ref(v_fst_532_);
v_a_548_ = lean_ctor_get(v_a_544_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v_a_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v_a_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v_a_552_; 
lean_del_object(v___x_546_);
v_a_552_ = lean_ctor_get(v_a_544_, 0);
lean_inc(v_a_552_);
lean_dec_ref(v_a_544_);
v_a_533_ = v_snd_541_;
v_b_534_ = v_a_552_;
goto _start;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_snd_541_);
lean_dec_ref(v_fst_532_);
v_a_555_ = lean_ctor_get(v___y_543_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___y_543_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___y_543_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___y_543_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_584_, lean_object* v_fst_585_, lean_object* v_a_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
uint8_t v_cancel_boxed_591_; lean_object* v_res_592_; 
v_cancel_boxed_591_ = lean_unbox(v_cancel_584_);
v_res_592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_boxed_591_, v_fst_585_, v_a_586_, v_b_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_592_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_593_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__0);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_ctor_set(v___x_598_, 3, v___x_597_);
lean_ctor_set(v___x_598_, 4, v___x_596_);
lean_ctor_set(v___x_598_, 5, v___x_596_);
lean_ctor_set(v___x_598_, 6, v___x_596_);
lean_ctor_set(v___x_598_, 7, v___x_596_);
lean_ctor_set(v___x_598_, 8, v___x_596_);
lean_ctor_set(v___x_598_, 9, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_unsigned_to_nat(32u);
v___x_600_ = lean_mk_empty_array_with_capacity(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_602_ = ((size_t)5ULL);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_unsigned_to_nat(32u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__3);
v___x_607_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_603_);
lean_ctor_set(v___x_607_, 3, v___x_603_);
lean_ctor_set_usize(v___x_607_, 4, v___x_602_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = lean_box(1);
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__4);
v___x_610_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__1);
v___x_611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(lean_object* v_msgData_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v_env_617_; lean_object* v_options_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_616_ = lean_st_ref_get(v___y_614_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_617_);
lean_dec(v___x_616_);
v_options_618_ = lean_ctor_get(v___y_613_, 2);
v___x_619_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__2);
v___x_620_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_618_);
v___x_621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_621_, 0, v_env_617_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_ctor_set(v___x_621_, 3, v_options_618_);
v___x_622_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_msgData_612_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msgData_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_ref_633_; lean_object* v___x_634_; lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
v_ref_633_ = lean_ctor_get(v___y_630_, 5);
v___x_634_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1_spec__1(v_msg_629_, v___y_630_, v___y_631_);
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
lean_inc(v_ref_633_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_ref_633_);
lean_ctor_set(v___x_639_, 1, v_a_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 1);
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_648_;
}
}
static lean_object* _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Core_CoreM_parFirst___redArg___closed__0));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg(lean_object* v_jobs_652_, uint8_t v_cancel_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Core_CoreM_parIterGreedyWithCancel___redArg(v_jobs_652_, v_a_654_, v_a_655_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref(v___x_657_);
v_fst_659_ = lean_ctor_get(v_a_658_, 0);
lean_inc(v_fst_659_);
v_snd_660_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_snd_660_);
lean_dec(v_a_658_);
v___x_661_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_662_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_653_, v_fst_659_, v_snd_660_, v___x_661_, v_a_654_, v_a_655_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_674_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_674_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v_fst_667_; 
v_fst_667_ = lean_ctor_get(v_a_663_, 0);
lean_inc(v_fst_667_);
lean_dec(v_a_663_);
if (lean_obj_tag(v_fst_667_) == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_del_object(v___x_665_);
v___x_668_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_669_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v___x_668_, v_a_654_, v_a_655_);
return v___x_669_;
}
else
{
lean_object* v_val_670_; lean_object* v___x_672_; 
v_val_670_ = lean_ctor_get(v_fst_667_, 0);
lean_inc(v_val_670_);
lean_dec_ref(v_fst_667_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v_val_670_);
v___x_672_ = v___x_665_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_val_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_662_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_662_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
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
v_a_683_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_657_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_657_);
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
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___redArg___boxed(lean_object* v_jobs_691_, lean_object* v_cancel_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
uint8_t v_cancel_boxed_696_; lean_object* v_res_697_; 
v_cancel_boxed_696_ = lean_unbox(v_cancel_692_);
v_res_697_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_691_, v_cancel_boxed_696_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst(lean_object* v_00_u03b1_698_, lean_object* v_jobs_699_, uint8_t v_cancel_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Core_CoreM_parFirst___redArg(v_jobs_699_, v_cancel_700_, v_a_701_, v_a_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_CoreM_parFirst___boxed(lean_object* v_00_u03b1_705_, lean_object* v_jobs_706_, lean_object* v_cancel_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
uint8_t v_cancel_boxed_711_; lean_object* v_res_712_; 
v_cancel_boxed_711_ = lean_unbox(v_cancel_707_);
v_res_712_ = l_Lean_Core_CoreM_parFirst(v_00_u03b1_705_, v_jobs_706_, v_cancel_boxed_711_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(lean_object* v_00_u03b1_713_, uint8_t v_cancel_714_, lean_object* v_fst_715_, lean_object* v_inst_716_, lean_object* v_R_717_, lean_object* v_a_718_, lean_object* v_b_719_, lean_object* v_c_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg(v_cancel_714_, v_fst_715_, v_a_718_, v_b_719_, v___y_721_, v___y_722_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_725_, lean_object* v_cancel_726_, lean_object* v_fst_727_, lean_object* v_inst_728_, lean_object* v_R_729_, lean_object* v_a_730_, lean_object* v_b_731_, lean_object* v_c_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v_cancel_boxed_736_; lean_object* v_res_737_; 
v_cancel_boxed_736_ = lean_unbox(v_cancel_726_);
v_res_737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0(v_00_u03b1_725_, v_cancel_boxed_736_, v_fst_727_, v_inst_728_, v_R_729_, v_a_730_, v_b_731_, v_c_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(lean_object* v_00_u03b1_738_, lean_object* v_msg_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___redArg(v_msg_739_, v___y_740_, v___y_741_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_744_, lean_object* v_msg_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_throwError___at___00Lean_Core_CoreM_parFirst_spec__1(v_00_u03b1_744_, v_msg_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = l_List_reverse___redArg(v_x_751_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
else
{
lean_object* v_head_759_; lean_object* v_tail_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_778_; 
v_head_759_ = lean_ctor_get(v_x_750_, 0);
v_tail_760_ = lean_ctor_get(v_x_750_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_750_);
if (v_isSharedCheck_778_ == 0)
{
v___x_762_ = v_x_750_;
v_isShared_763_ = v_isSharedCheck_778_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_tail_760_);
lean_inc(v_head_759_);
lean_dec(v_x_750_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_778_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Meta_MetaM_asTask_x27___redArg(v_head_759_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref(v___x_764_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v_x_751_);
lean_ctor_set(v___x_762_, 0, v_a_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_x_751_);
v___x_767_ = v_reuseFailAlloc_769_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
v_x_750_ = v_tail_760_;
v_x_751_ = v___x_767_;
goto _start;
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_del_object(v___x_762_);
lean_dec(v_tail_760_);
lean_dec(v_x_751_);
v_a_770_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_764_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_764_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg___boxed(lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_779_, v_x_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(lean_object* v_as_x27_787_, lean_object* v_b_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
if (lean_obj_tag(v_as_x27_787_) == 0)
{
lean_object* v___x_794_; 
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v_b_788_);
return v___x_794_;
}
else
{
lean_object* v_head_795_; lean_object* v_tail_796_; lean_object* v_a_798_; lean_object* v___y_802_; uint8_t v___y_803_; lean_object* v_a_807_; lean_object* v___x_2329__overap_810_; lean_object* v___x_811_; 
v_head_795_ = lean_ctor_get(v_as_x27_787_, 0);
v_tail_796_ = lean_ctor_get(v_as_x27_787_, 1);
lean_inc(v_head_795_);
v___x_2329__overap_810_ = lean_task_get_own(v_head_795_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
v___x_811_ = lean_apply_5(v___x_2329__overap_810_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, lean_box(0));
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = l_Lean_Meta_saveState___redArg(v___y_790_, v___y_792_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_822_ == 0)
{
v___x_816_ = v___x_813_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v_a_812_);
lean_ctor_set(v___x_818_, 1, v_a_814_);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 1);
lean_ctor_set(v___x_816_, 0, v___x_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
v_a_798_ = v___x_820_;
goto v___jp_797_;
}
}
}
else
{
lean_object* v_a_823_; 
lean_dec(v_a_812_);
v_a_823_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_823_);
lean_dec_ref(v___x_813_);
v_a_807_ = v_a_823_;
goto v___jp_806_;
}
}
else
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_824_);
lean_dec_ref(v___x_811_);
v_a_807_ = v_a_824_;
goto v___jp_806_;
}
v___jp_797_:
{
lean_object* v___x_799_; 
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v_a_798_);
lean_ctor_set(v___x_799_, 1, v_b_788_);
v_as_x27_787_ = v_tail_796_;
v_b_788_ = v___x_799_;
goto _start;
}
v___jp_801_:
{
if (v___y_803_ == 0)
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___y_802_);
v_a_798_ = v___x_804_;
goto v___jp_797_;
}
else
{
lean_object* v___x_805_; 
lean_dec(v_b_788_);
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v___y_802_);
return v___x_805_;
}
}
v___jp_806_:
{
uint8_t v___x_808_; 
v___x_808_ = l_Lean_Exception_isInterrupt(v_a_807_);
if (v___x_808_ == 0)
{
uint8_t v___x_809_; 
lean_inc_ref(v_a_807_);
v___x_809_ = l_Lean_Exception_isRuntime(v_a_807_);
v___y_802_ = v_a_807_;
v___y_803_ = v___x_809_;
goto v___jp_801_;
}
else
{
v___y_802_ = v_a_807_;
v___y_803_ = v___x_808_;
goto v___jp_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg___boxed(lean_object* v_as_x27_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_825_, v_b_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v_as_x27_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg(lean_object* v_jobs_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_st_ref_get(v_a_835_);
v___x_840_ = lean_box(0);
v___x_841_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_833_, v___x_840_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_841_);
v___x_843_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_a_842_, v___x_840_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_842_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_853_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_853_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = lean_st_ref_set(v_a_835_, v___x_839_);
v___x_849_ = l_List_reverse___redArg(v_a_844_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_dec(v___x_839_);
return v___x_843_;
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v___x_839_);
v_a_854_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_841_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_841_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___redArg___boxed(lean_object* v_jobs_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par(lean_object* v_00_u03b1_869_, lean_object* v_jobs_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_MetaM_par___redArg(v_jobs_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par___boxed(lean_object* v_00_u03b1_877_, lean_object* v_jobs_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Meta_MetaM_par(v_00_u03b1_877_, v_jobs_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(lean_object* v_00_u03b1_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_x_886_, v_x_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___boxed(lean_object* v_00_u03b1_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0(v_00_u03b1_894_, v_x_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(lean_object* v_00_u03b1_903_, lean_object* v_as_904_, lean_object* v_as_x27_905_, lean_object* v_b_906_, lean_object* v_a_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___redArg(v_as_x27_905_, v_b_906_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1___boxed(lean_object* v_00_u03b1_914_, lean_object* v_as_915_, lean_object* v_as_x27_916_, lean_object* v_b_917_, lean_object* v_a_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_spec__1(v_00_u03b1_914_, v_as_915_, v_as_x27_916_, v_b_917_, v_a_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v_as_x27_916_);
lean_dec(v_as_915_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(lean_object* v_as_x27_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
if (lean_obj_tag(v_as_x27_925_) == 0)
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v_b_926_);
return v___x_932_;
}
else
{
lean_object* v_head_933_; lean_object* v_tail_934_; lean_object* v___x_2032__overap_935_; lean_object* v___x_936_; 
v_head_933_ = lean_ctor_get(v_as_x27_925_, 0);
v_tail_934_ = lean_ctor_get(v_as_x27_925_, 1);
lean_inc(v_head_933_);
v___x_2032__overap_935_ = lean_task_get_own(v_head_933_);
lean_inc(v___y_930_);
lean_inc_ref(v___y_929_);
lean_inc(v___y_928_);
lean_inc_ref(v___y_927_);
v___x_936_ = lean_apply_5(v___x_2032__overap_935_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, lean_box(0));
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v_a_937_);
v___x_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v_b_926_);
v_as_x27_925_ = v_tail_934_;
v_b_926_ = v___x_939_;
goto _start;
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_955_; 
v_a_941_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_955_ == 0)
{
v___x_943_ = v___x_936_;
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_936_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_955_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
uint8_t v___y_946_; uint8_t v___x_953_; 
v___x_953_ = l_Lean_Exception_isInterrupt(v_a_941_);
if (v___x_953_ == 0)
{
uint8_t v___x_954_; 
lean_inc(v_a_941_);
v___x_954_ = l_Lean_Exception_isRuntime(v_a_941_);
v___y_946_ = v___x_954_;
goto v___jp_945_;
}
else
{
v___y_946_ = v___x_953_;
goto v___jp_945_;
}
v___jp_945_:
{
if (v___y_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_del_object(v___x_943_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_a_941_);
v___x_948_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v_b_926_);
v_as_x27_925_ = v_tail_934_;
v_b_926_ = v___x_948_;
goto _start;
}
else
{
lean_object* v___x_951_; 
lean_dec(v_b_926_);
if (v_isShared_944_ == 0)
{
v___x_951_ = v___x_943_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_941_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_956_, lean_object* v_b_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_956_, v_b_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v_as_x27_956_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg(lean_object* v_jobs_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = lean_st_ref_get(v_a_966_);
v___x_971_ = lean_box(0);
v___x_972_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_par_spec__0___redArg(v_jobs_964_, v___x_971_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_a_973_, v___x_971_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_984_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_984_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_984_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = lean_st_ref_set(v_a_966_, v___x_970_);
v___x_980_ = l_List_reverse___redArg(v_a_975_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
lean_dec(v___x_970_);
return v___x_974_;
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v___x_970_);
v_a_985_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_972_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_972_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___redArg___boxed(lean_object* v_jobs_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27(lean_object* v_00_u03b1_1000_, lean_object* v_jobs_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_MetaM_par_x27___redArg(v_jobs_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_par_x27___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_jobs_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Meta_MetaM_par_x27(v_00_u03b1_1008_, v_jobs_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(lean_object* v_00_u03b1_1016_, lean_object* v_as_1017_, lean_object* v_as_x27_1018_, lean_object* v_b_1019_, lean_object* v_a_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___redArg(v_as_x27_1018_, v_b_1019_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_1027_, lean_object* v_as_1028_, lean_object* v_as_x27_1029_, lean_object* v_b_1030_, lean_object* v_a_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_List_forIn_x27_loop___at___00Lean_Meta_MetaM_par_x27_spec__0(v_00_u03b1_1027_, v_as_1028_, v_as_x27_1029_, v_b_1030_, v_a_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v_as_x27_1029_);
lean_dec(v_as_1028_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = l_List_reverse___redArg(v_x_1039_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v_head_1047_; lean_object* v_tail_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1066_; 
v_head_1047_ = lean_ctor_get(v_x_1038_, 0);
v_tail_1048_ = lean_ctor_get(v_x_1038_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1038_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1050_ = v_x_1038_;
v_isShared_1051_ = v_isSharedCheck_1066_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_tail_1048_);
lean_inc(v_head_1047_);
lean_dec(v_x_1038_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1066_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Meta_MetaM_asTask___redArg(v_head_1047_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v_x_1039_);
lean_ctor_set(v___x_1050_, 0, v_a_1053_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_x_1039_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
v_x_1038_ = v_tail_1048_;
v_x_1039_ = v___x_1055_;
goto _start;
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_del_object(v___x_1050_);
lean_dec(v_tail_1048_);
lean_dec(v_x_1039_);
v_a_1058_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_1052_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_1052_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1067_, v_x_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg(lean_object* v_jobs_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1075_, v___x_1081_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1101_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1101_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1101_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v_fst_1088_; lean_object* v_snd_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1100_; 
v___x_1087_ = l_List_unzipTR___redArg(v_a_1083_);
v_fst_1088_ = lean_ctor_get(v___x_1087_, 0);
v_snd_1089_ = lean_ctor_get(v___x_1087_, 1);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1091_ = v___x_1087_;
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_snd_1089_);
lean_inc(v_fst_1088_);
lean_dec(v___x_1087_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1093_, 0, v_fst_1088_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_snd_1089_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1095_);
v___x_1097_ = v___x_1085_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1082_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1082_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel(lean_object* v_00_u03b1_1117_, lean_object* v_jobs_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_jobs_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_MetaM_parIterWithCancel(v_00_u03b1_1125_, v_jobs_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_x_1134_, v_x_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0(v_00_u03b1_1142_, v_x_1143_, v_x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg(lean_object* v_jobs_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_Meta_MetaM_parIterWithCancel___redArg(v_jobs_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1166_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_snd_1162_; lean_object* v___x_1164_; 
v_snd_1162_ = lean_ctor_get(v_a_1158_, 1);
lean_inc(v_snd_1162_);
lean_dec(v_a_1158_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v_snd_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_snd_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1157_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1157_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___redArg___boxed(lean_object* v_jobs_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter(lean_object* v_00_u03b1_1182_, lean_object* v_jobs_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_MetaM_parIter___redArg(v_jobs_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIter___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_jobs_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Meta_MetaM_parIter(v_00_u03b1_1190_, v_jobs_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = l_List_mapM_loop___at___00Lean_Meta_MetaM_parIterWithCancel_spec__0___redArg(v_jobs_1198_, v___x_1204_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1224_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1224_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1224_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1223_; 
v___x_1210_ = l_List_unzipTR___redArg(v_a_1206_);
v_fst_1211_ = lean_ctor_get(v___x_1210_, 0);
v_snd_1212_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1214_ = v___x_1210_;
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snd_1212_);
lean_inc(v_fst_1211_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1216_, 0, v_fst_1211_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_snd_1212_);
v___x_1218_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
lean_object* v___x_1220_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1218_);
v___x_1220_ = v___x_1208_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
v_a_1225_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1205_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1205_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1240_, lean_object* v_jobs_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_jobs_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel(v_00_u03b1_1248_, v_jobs_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg(lean_object* v_jobs_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_snd_1267_; lean_object* v___x_1269_; 
v_snd_1267_ = lean_ctor_get(v_a_1263_, 1);
lean_inc(v_snd_1267_);
lean_dec(v_a_1263_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v_snd_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_snd_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
v_a_1272_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1262_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1262_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy(lean_object* v_00_u03b1_1287_, lean_object* v_jobs_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_Meta_MetaM_parIterGreedy___redArg(v_jobs_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parIterGreedy___boxed(lean_object* v_00_u03b1_1295_, lean_object* v_jobs_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Meta_MetaM_parIterGreedy(v_00_u03b1_1295_, v_jobs_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_1303_, lean_object* v___x_1304_, lean_object* v_____r_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_a_1303_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1304_);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
v___x_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_1315_, lean_object* v___x_1316_, lean_object* v_____r_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1315_, v___x_1316_, v_____r_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(uint8_t v_cancel_1324_, lean_object* v_fst_1325_, lean_object* v_a_1326_, lean_object* v_b_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
if (lean_obj_tag(v_a_1326_) == 0)
{
lean_object* v___x_1333_; 
lean_dec_ref(v_fst_1325_);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v_b_1327_);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; lean_object* v_fst_1335_; lean_object* v_snd_1336_; lean_object* v___y_1338_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec_ref(v_b_1327_);
v___x_1334_ = l_IO_waitAny_x27___redArg(v_a_1326_);
v_fst_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_fst_1335_);
v_snd_1336_ = lean_ctor_get(v___x_1334_, 1);
lean_inc(v_snd_1336_);
lean_dec_ref(v___x_1334_);
v___x_1358_ = lean_box(0);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1329_);
lean_inc_ref(v___y_1328_);
v___x_1359_ = lean_apply_5(v_fst_1335_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, lean_box(0));
if (lean_obj_tag(v___x_1359_) == 0)
{
if (v_cancel_1324_ == 0)
{
lean_object* v_a_1360_; lean_object* v___x_1361_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref(v___x_1359_);
v___x_1361_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1360_, v___x_1358_, v___x_1358_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
v___y_1338_ = v___x_1361_;
goto v___jp_1337_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_a_1362_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1362_);
lean_dec_ref(v___x_1359_);
lean_inc_ref(v_fst_1325_);
v___x_1363_ = lean_apply_1(v_fst_1325_, lean_box(0));
v___x_1364_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___lam__0(v_a_1362_, v___x_1358_, v___x_1363_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
v___y_1338_ = v___x_1364_;
goto v___jp_1337_;
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1378_; 
v_a_1365_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1367_ = v___x_1359_;
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1359_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1378_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; uint8_t v___y_1371_; uint8_t v___x_1376_; 
v___x_1369_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1376_ = l_Lean_Exception_isInterrupt(v_a_1365_);
if (v___x_1376_ == 0)
{
uint8_t v___x_1377_; 
lean_inc(v_a_1365_);
v___x_1377_ = l_Lean_Exception_isRuntime(v_a_1365_);
v___y_1371_ = v___x_1377_;
goto v___jp_1370_;
}
else
{
v___y_1371_ = v___x_1376_;
goto v___jp_1370_;
}
v___jp_1370_:
{
if (v___y_1371_ == 0)
{
lean_del_object(v___x_1367_);
lean_dec(v_a_1365_);
v_a_1326_ = v_snd_1336_;
v_b_1327_ = v___x_1369_;
goto _start;
}
else
{
lean_object* v___x_1374_; 
lean_dec(v_snd_1336_);
lean_dec_ref(v_fst_1325_);
if (v_isShared_1368_ == 0)
{
v___x_1374_ = v___x_1367_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1365_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
v___jp_1337_:
{
if (lean_obj_tag(v___y_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1349_; 
v_a_1339_ = lean_ctor_get(v___y_1338_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___y_1338_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1341_ = v___y_1338_;
v_isShared_1342_ = v_isSharedCheck_1349_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___y_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1349_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
if (lean_obj_tag(v_a_1339_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; 
lean_dec(v_snd_1336_);
lean_dec_ref(v_fst_1325_);
v_a_1343_ = lean_ctor_get(v_a_1339_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v_a_1339_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_a_1343_);
v___x_1345_ = v___x_1341_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
else
{
lean_object* v_a_1347_; 
lean_del_object(v___x_1341_);
v_a_1347_ = lean_ctor_get(v_a_1339_, 0);
lean_inc(v_a_1347_);
lean_dec_ref(v_a_1339_);
v_a_1326_ = v_snd_1336_;
v_b_1327_ = v_a_1347_;
goto _start;
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_snd_1336_);
lean_dec_ref(v_fst_1325_);
v_a_1350_ = lean_ctor_get(v___y_1338_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___y_1338_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___y_1338_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___y_1338_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_1379_, lean_object* v_fst_1380_, lean_object* v_a_1381_, lean_object* v_b_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v_cancel_boxed_1388_; lean_object* v_res_1389_; 
v_cancel_boxed_1388_ = lean_unbox(v_cancel_1379_);
v_res_1389_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_boxed_1388_, v_fst_1380_, v_a_1381_, v_b_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(lean_object* v_msgData_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; lean_object* v_env_1397_; lean_object* v___x_1398_; lean_object* v_mctx_1399_; lean_object* v_lctx_1400_; lean_object* v_options_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1396_ = lean_st_ref_get(v___y_1394_);
v_env_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_ref(v_env_1397_);
lean_dec(v___x_1396_);
v___x_1398_ = lean_st_ref_get(v___y_1392_);
v_mctx_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc_ref(v_mctx_1399_);
lean_dec(v___x_1398_);
v_lctx_1400_ = lean_ctor_get(v___y_1391_, 2);
v_options_1401_ = lean_ctor_get(v___y_1393_, 2);
lean_inc_ref(v_options_1401_);
lean_inc_ref(v_lctx_1400_);
v___x_1402_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1402_, 0, v_env_1397_);
lean_ctor_set(v___x_1402_, 1, v_mctx_1399_);
lean_ctor_set(v___x_1402_, 2, v_lctx_1400_);
lean_ctor_set(v___x_1402_, 3, v_options_1401_);
v___x_1403_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v_msgData_1390_);
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msgData_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_ref_1418_; lean_object* v___x_1419_; lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1428_; 
v_ref_1418_ = lean_ctor_get(v___y_1415_, 5);
v___x_1419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_inc(v_ref_1418_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_ref_1418_);
lean_ctor_set(v___x_1424_, 1, v_a_1420_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg(lean_object* v_jobs_1436_, uint8_t v_cancel_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Meta_MetaM_parIterGreedyWithCancel___redArg(v_jobs_1436_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v_fst_1445_; lean_object* v_snd_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref(v___x_1443_);
v_fst_1445_ = lean_ctor_get(v_a_1444_, 0);
lean_inc(v_fst_1445_);
v_snd_1446_ = lean_ctor_get(v_a_1444_, 1);
lean_inc(v_snd_1446_);
lean_dec(v_a_1444_);
v___x_1447_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_1448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1437_, v_fst_1445_, v_snd_1446_, v___x_1447_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1460_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1460_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_fst_1453_; 
v_fst_1453_ = lean_ctor_get(v_a_1449_, 0);
lean_inc(v_fst_1453_);
lean_dec(v_a_1449_);
if (lean_obj_tag(v_fst_1453_) == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_del_object(v___x_1451_);
v___x_1454_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_1455_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v___x_1454_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v___x_1455_;
}
else
{
lean_object* v_val_1456_; lean_object* v___x_1458_; 
v_val_1456_ = lean_ctor_get(v_fst_1453_, 0);
lean_inc(v_val_1456_);
lean_dec_ref(v_fst_1453_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v_val_1456_);
v___x_1458_ = v___x_1451_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_val_1456_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
v_a_1461_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1448_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1448_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
v_a_1469_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1443_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1443_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___redArg___boxed(lean_object* v_jobs_1477_, lean_object* v_cancel_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_){
_start:
{
uint8_t v_cancel_boxed_1484_; lean_object* v_res_1485_; 
v_cancel_boxed_1484_ = lean_unbox(v_cancel_1478_);
v_res_1485_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1477_, v_cancel_boxed_1484_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
lean_dec(v_a_1482_);
lean_dec_ref(v_a_1481_);
lean_dec(v_a_1480_);
lean_dec_ref(v_a_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst(lean_object* v_00_u03b1_1486_, lean_object* v_jobs_1487_, uint8_t v_cancel_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Meta_MetaM_parFirst___redArg(v_jobs_1487_, v_cancel_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MetaM_parFirst___boxed(lean_object* v_00_u03b1_1495_, lean_object* v_jobs_1496_, lean_object* v_cancel_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
uint8_t v_cancel_boxed_1503_; lean_object* v_res_1504_; 
v_cancel_boxed_1503_ = lean_unbox(v_cancel_1497_);
v_res_1504_ = l_Lean_Meta_MetaM_parFirst(v_00_u03b1_1495_, v_jobs_1496_, v_cancel_boxed_1503_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(lean_object* v_00_u03b1_1505_, uint8_t v_cancel_1506_, lean_object* v_fst_1507_, lean_object* v_inst_1508_, lean_object* v_R_1509_, lean_object* v_a_1510_, lean_object* v_b_1511_, lean_object* v_c_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___redArg(v_cancel_1506_, v_fst_1507_, v_a_1510_, v_b_1511_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_1519_, lean_object* v_cancel_1520_, lean_object* v_fst_1521_, lean_object* v_inst_1522_, lean_object* v_R_1523_, lean_object* v_a_1524_, lean_object* v_b_1525_, lean_object* v_c_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_cancel_boxed_1532_; lean_object* v_res_1533_; 
v_cancel_boxed_1532_ = lean_unbox(v_cancel_1520_);
v_res_1533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MetaM_parFirst_spec__0(v_00_u03b1_1519_, v_cancel_boxed_1532_, v_fst_1521_, v_inst_1522_, v_R_1523_, v_a_1524_, v_b_1525_, v_c_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(lean_object* v_00_u03b1_1534_, lean_object* v_msg_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___redArg(v_msg_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_msg_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1(v_00_u03b1_1542_, v_msg_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(lean_object* v_x_1550_, lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_List_reverse___redArg(v_x_1551_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
return v___x_1560_;
}
else
{
lean_object* v_head_1561_; lean_object* v_tail_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1580_; 
v_head_1561_ = lean_ctor_get(v_x_1550_, 0);
v_tail_1562_ = lean_ctor_get(v_x_1550_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_x_1550_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1564_ = v_x_1550_;
v_isShared_1565_ = v_isSharedCheck_1580_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_tail_1562_);
lean_inc(v_head_1561_);
lean_dec(v_x_1550_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1580_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Elab_Term_TermElabM_asTask___redArg(v_head_1561_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v_x_1551_);
lean_ctor_set(v___x_1564_, 0, v_a_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1567_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_x_1551_);
v___x_1569_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
v_x_1550_ = v_tail_1562_;
v_x_1551_ = v___x_1569_;
goto _start;
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1564_);
lean_dec(v_tail_1562_);
lean_dec(v_x_1551_);
v_a_1572_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1566_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1566_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_1581_, lean_object* v_x_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1581_, v_x_1582_, v___y_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(lean_object* v_jobs_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1591_, v___x_1599_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1619_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1603_ = v___x_1600_;
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v_fst_1606_; lean_object* v_snd_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1618_; 
v___x_1605_ = l_List_unzipTR___redArg(v_a_1601_);
v_fst_1606_ = lean_ctor_get(v___x_1605_, 0);
v_snd_1607_ = lean_ctor_get(v___x_1605_, 1);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1609_ = v___x_1605_;
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_snd_1607_);
lean_inc(v_fst_1606_);
lean_dec(v___x_1605_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1618_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1611_, 0, v_fst_1606_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1611_);
v___x_1613_ = v___x_1609_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_snd_1607_);
v___x_1613_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1615_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 0, v___x_1613_);
v___x_1615_ = v___x_1603_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1600_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1600_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec(v_a_1634_);
lean_dec_ref(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel(lean_object* v_00_u03b1_1637_, lean_object* v_jobs_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterWithCancel___boxed(lean_object* v_00_u03b1_1647_, lean_object* v_jobs_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel(v_00_u03b1_1647_, v_jobs_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_x_1658_, v_x_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0(v_00_u03b1_1668_, v_x_1669_, v_x_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg(lean_object* v_jobs_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Elab_Term_TermElabM_parIterWithCancel___redArg(v_jobs_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1696_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1696_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_snd_1692_; lean_object* v___x_1694_; 
v_snd_1692_ = lean_ctor_get(v_a_1688_, 1);
lean_inc(v_snd_1692_);
lean_dec(v_a_1688_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v_snd_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_snd_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
v_a_1697_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1687_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1687_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___redArg___boxed(lean_object* v_jobs_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
lean_dec_ref(v_a_1706_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter(lean_object* v_00_u03b1_1714_, lean_object* v_jobs_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_Lean_Elab_Term_TermElabM_parIter___redArg(v_jobs_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIter___boxed(lean_object* v_00_u03b1_1724_, lean_object* v_jobs_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Elab_Term_TermElabM_parIter(v_00_u03b1_1724_, v_jobs_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_box(0);
v___x_1743_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_parIterWithCancel_spec__0___redArg(v_jobs_1734_, v___x_1742_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1762_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1746_ = v___x_1743_;
v_isShared_1747_ = v_isSharedCheck_1762_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1743_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1762_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1761_; 
v___x_1748_ = l_List_unzipTR___redArg(v_a_1744_);
v_fst_1749_ = lean_ctor_get(v___x_1748_, 0);
v_snd_1750_ = lean_ctor_get(v___x_1748_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1752_ = v___x_1748_;
v_isShared_1753_ = v_isSharedCheck_1761_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_snd_1750_);
lean_inc(v_fst_1749_);
lean_dec(v___x_1748_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1761_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1754_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_1754_, 0, v_fst_1749_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1756_ = v___x_1752_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_snd_1750_);
v___x_1756_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
lean_object* v___x_1758_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1756_);
v___x_1758_ = v___x_1746_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
v_a_1763_ = lean_ctor_get(v___x_1743_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1743_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1743_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(lean_object* v_00_u03b1_1780_, lean_object* v_jobs_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_jobs_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel(v_00_u03b1_1790_, v_jobs_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(lean_object* v_jobs_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1817_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1817_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_snd_1813_; lean_object* v___x_1815_; 
v_snd_1813_ = lean_ctor_get(v_a_1809_, 1);
lean_inc(v_snd_1813_);
lean_dec(v_a_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v_snd_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_snd_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_a_1818_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1808_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1808_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg___boxed(lean_object* v_jobs_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec(v_a_1828_);
lean_dec_ref(v_a_1827_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy(lean_object* v_00_u03b1_1835_, lean_object* v_jobs_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_Elab_Term_TermElabM_parIterGreedy___redArg(v_jobs_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parIterGreedy___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_jobs_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Elab_Term_TermElabM_parIterGreedy(v_00_u03b1_1845_, v_jobs_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = l_List_reverse___redArg(v_x_1856_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
else
{
lean_object* v_head_1866_; lean_object* v_tail_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1885_; 
v_head_1866_ = lean_ctor_get(v_x_1855_, 0);
v_tail_1867_ = lean_ctor_get(v_x_1855_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1855_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1869_ = v_x_1855_;
v_isShared_1870_ = v_isSharedCheck_1885_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_tail_1867_);
lean_inc(v_head_1866_);
lean_dec(v_x_1855_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1885_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_Lean_Elab_Term_TermElabM_asTask_x27___redArg(v_head_1866_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1871_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v_x_1856_);
lean_ctor_set(v___x_1869_, 0, v_a_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1872_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_x_1856_);
v___x_1874_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
v_x_1855_ = v_tail_1867_;
v_x_1856_ = v___x_1874_;
goto _start;
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_del_object(v___x_1869_);
lean_dec(v_tail_1867_);
lean_dec(v_x_1856_);
v_a_1877_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1871_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1871_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg___boxed(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_1886_, v_x_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(lean_object* v_as_x27_1896_, lean_object* v_b_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
if (lean_obj_tag(v_as_x27_1896_) == 0)
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_b_1897_);
return v___x_1905_;
}
else
{
lean_object* v_head_1906_; lean_object* v_tail_1907_; lean_object* v___y_1909_; uint8_t v___y_1910_; lean_object* v_a_1916_; lean_object* v___x_2960__overap_1919_; lean_object* v___x_1920_; 
v_head_1906_ = lean_ctor_get(v_as_x27_1896_, 0);
v_tail_1907_ = lean_ctor_get(v_as_x27_1896_, 1);
lean_inc(v_head_1906_);
v___x_2960__overap_1919_ = lean_task_get_own(v_head_1906_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1900_);
lean_inc(v___y_1899_);
lean_inc_ref(v___y_1898_);
v___x_1920_ = lean_apply_7(v___x_2960__overap_1919_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, lean_box(0));
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
v___x_1922_ = l_Lean_Elab_Term_saveState___redArg(v___y_1899_, v___y_1901_, v___y_1903_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1933_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1933_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_a_1921_);
lean_ctor_set(v___x_1927_, 1, v_a_1923_);
if (v_isShared_1926_ == 0)
{
lean_ctor_set_tag(v___x_1925_, 1);
lean_ctor_set(v___x_1925_, 0, v___x_1927_);
v___x_1929_ = v___x_1925_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_b_1897_);
v_as_x27_1896_ = v_tail_1907_;
v_b_1897_ = v___x_1930_;
goto _start;
}
}
}
else
{
lean_object* v_a_1934_; 
lean_dec(v_a_1921_);
v_a_1934_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1934_);
lean_dec_ref(v___x_1922_);
v_a_1916_ = v_a_1934_;
goto v___jp_1915_;
}
}
else
{
lean_object* v_a_1935_; 
v_a_1935_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1920_);
v_a_1916_ = v_a_1935_;
goto v___jp_1915_;
}
v___jp_1908_:
{
if (v___y_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___y_1909_);
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v_b_1897_);
v_as_x27_1896_ = v_tail_1907_;
v_b_1897_ = v___x_1912_;
goto _start;
}
else
{
lean_object* v___x_1914_; 
lean_dec(v_b_1897_);
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v___y_1909_);
return v___x_1914_;
}
}
v___jp_1915_:
{
uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Exception_isInterrupt(v_a_1916_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
lean_inc_ref(v_a_1916_);
v___x_1918_ = l_Lean_Exception_isRuntime(v_a_1916_);
v___y_1909_ = v_a_1916_;
v___y_1910_ = v___x_1918_;
goto v___jp_1908_;
}
else
{
v___y_1909_ = v_a_1916_;
v___y_1910_ = v___x_1917_;
goto v___jp_1908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg___boxed(lean_object* v_as_x27_1936_, lean_object* v_b_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_1936_, v_b_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v_as_x27_1936_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg(lean_object* v_jobs_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_st_ref_get(v_a_1948_);
v___x_1955_ = lean_box(0);
v___x_1956_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_1946_, v___x_1955_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; lean_object* v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
v___x_1958_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_a_1957_, v___x_1955_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1957_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1968_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1968_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1963_ = lean_st_ref_set(v_a_1948_, v___x_1954_);
v___x_1964_ = l_List_reverse___redArg(v_a_1959_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1964_);
v___x_1966_ = v___x_1961_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
else
{
lean_dec(v___x_1954_);
return v___x_1958_;
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v___x_1954_);
v_a_1969_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1956_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1956_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___redArg___boxed(lean_object* v_jobs_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par(lean_object* v_00_u03b1_1986_, lean_object* v_jobs_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l_Lean_Elab_Term_TermElabM_par___redArg(v_jobs_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par___boxed(lean_object* v_00_u03b1_1996_, lean_object* v_jobs_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Lean_Elab_Term_TermElabM_par(v_00_u03b1_1996_, v_jobs_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(lean_object* v_00_u03b1_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_x_2007_, v_x_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___boxed(lean_object* v_00_u03b1_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0(v_00_u03b1_2017_, v_x_2018_, v_x_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(lean_object* v_00_u03b1_2028_, lean_object* v_as_2029_, lean_object* v_as_x27_2030_, lean_object* v_b_2031_, lean_object* v_a_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___redArg(v_as_x27_2030_, v_b_2031_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1___boxed(lean_object* v_00_u03b1_2041_, lean_object* v_as_2042_, lean_object* v_as_x27_2043_, lean_object* v_b_2044_, lean_object* v_a_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_spec__1(v_00_u03b1_2041_, v_as_2042_, v_as_x27_2043_, v_b_2044_, v_a_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v_as_x27_2043_);
lean_dec(v_as_2042_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(lean_object* v_as_x27_2054_, lean_object* v_b_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
if (lean_obj_tag(v_as_x27_2054_) == 0)
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2063_, 0, v_b_2055_);
return v___x_2063_;
}
else
{
lean_object* v_head_2064_; lean_object* v_tail_2065_; lean_object* v___x_2570__overap_2066_; lean_object* v___x_2067_; 
v_head_2064_ = lean_ctor_get(v_as_x27_2054_, 0);
v_tail_2065_ = lean_ctor_get(v_as_x27_2054_, 1);
lean_inc(v_head_2064_);
v___x_2570__overap_2066_ = lean_task_get_own(v_head_2064_);
lean_inc(v___y_2061_);
lean_inc_ref(v___y_2060_);
lean_inc(v___y_2059_);
lean_inc_ref(v___y_2058_);
lean_inc(v___y_2057_);
lean_inc_ref(v___y_2056_);
v___x_2067_ = lean_apply_7(v___x_2570__overap_2066_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, lean_box(0));
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
v___x_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_a_2068_);
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v_b_2055_);
v_as_x27_2054_ = v_tail_2065_;
v_b_2055_ = v___x_2070_;
goto _start;
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2086_; 
v_a_2072_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2074_ = v___x_2067_;
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2067_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2086_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
uint8_t v___y_2077_; uint8_t v___x_2084_; 
v___x_2084_ = l_Lean_Exception_isInterrupt(v_a_2072_);
if (v___x_2084_ == 0)
{
uint8_t v___x_2085_; 
lean_inc(v_a_2072_);
v___x_2085_ = l_Lean_Exception_isRuntime(v_a_2072_);
v___y_2077_ = v___x_2085_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v___x_2084_;
goto v___jp_2076_;
}
v___jp_2076_:
{
if (v___y_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_del_object(v___x_2074_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_a_2072_);
v___x_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_b_2055_);
v_as_x27_2054_ = v_tail_2065_;
v_b_2055_ = v___x_2079_;
goto _start;
}
else
{
lean_object* v___x_2082_; 
lean_dec(v_b_2055_);
if (v_isShared_2075_ == 0)
{
v___x_2082_ = v___x_2074_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2072_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_2087_, lean_object* v_b_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2087_, v_b_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v_as_x27_2087_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg(lean_object* v_jobs_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = lean_st_ref_get(v_a_2099_);
v___x_2106_ = lean_box(0);
v___x_2107_ = l_List_mapM_loop___at___00Lean_Elab_Term_TermElabM_par_spec__0___redArg(v_jobs_2097_, v___x_2106_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_a_2108_, v___x_2106_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2108_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2119_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2114_ = lean_st_ref_set(v_a_2099_, v___x_2105_);
v___x_2115_ = l_List_reverse___redArg(v_a_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_dec(v___x_2105_);
return v___x_2109_;
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v___x_2105_);
v_a_2120_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2107_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2107_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___redArg___boxed(lean_object* v_jobs_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27(lean_object* v_00_u03b1_2137_, lean_object* v_jobs_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Elab_Term_TermElabM_par_x27___redArg(v_jobs_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_par_x27___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_jobs_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_Elab_Term_TermElabM_par_x27(v_00_u03b1_2147_, v_jobs_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(lean_object* v_00_u03b1_2157_, lean_object* v_as_2158_, lean_object* v_as_x27_2159_, lean_object* v_b_2160_, lean_object* v_a_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___redArg(v_as_x27_2159_, v_b_2160_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_2170_, lean_object* v_as_2171_, lean_object* v_as_x27_2172_, lean_object* v_b_2173_, lean_object* v_a_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_TermElabM_par_x27_spec__0(v_00_u03b1_2170_, v_as_2171_, v_as_x27_2172_, v_b_2173_, v_a_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v_as_x27_2172_);
lean_dec(v_as_2171_);
return v_res_2182_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = lean_box(1);
v___x_2184_ = l_Lean_MessageData_ofFormat(v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__2));
v___x_2189_ = l_Lean_MessageData_ofFormat(v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2191_) == 0)
{
return v_x_2190_;
}
else
{
lean_object* v_head_2192_; lean_object* v_tail_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2215_; 
v_head_2192_ = lean_ctor_get(v_x_2191_, 0);
v_tail_2193_ = lean_ctor_get(v_x_2191_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_x_2191_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2195_ = v_x_2191_;
v_isShared_2196_ = v_isSharedCheck_2215_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_tail_2193_);
lean_inc(v_head_2192_);
lean_dec(v_x_2191_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2215_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_before_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2213_; 
v_before_2197_ = lean_ctor_get(v_head_2192_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_head_2192_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; 
v_unused_2214_ = lean_ctor_get(v_head_2192_, 1);
lean_dec(v_unused_2214_);
v___x_2199_ = v_head_2192_;
v_isShared_2200_ = v_isSharedCheck_2213_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_before_2197_);
lean_dec(v_head_2192_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2213_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2200_ == 0)
{
lean_ctor_set_tag(v___x_2199_, 7);
lean_ctor_set(v___x_2199_, 1, v___x_2201_);
lean_ctor_set(v___x_2199_, 0, v_x_2190_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_x_2190_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__3);
if (v_isShared_2196_ == 0)
{
lean_ctor_set_tag(v___x_2195_, 7);
lean_ctor_set(v___x_2195_, 1, v___x_2204_);
lean_ctor_set(v___x_2195_, 0, v___x_2203_);
v___x_2206_ = v___x_2195_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = l_Lean_MessageData_ofSyntax(v_before_2197_);
v___x_2208_ = l_Lean_indentD(v___x_2207_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2206_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v_x_2190_ = v___x_2209_;
v_x_2191_ = v_tail_2193_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(lean_object* v_opts_2216_, lean_object* v_opt_2217_){
_start:
{
lean_object* v_name_2218_; lean_object* v_defValue_2219_; lean_object* v_map_2220_; lean_object* v___x_2221_; 
v_name_2218_ = lean_ctor_get(v_opt_2217_, 0);
v_defValue_2219_ = lean_ctor_get(v_opt_2217_, 1);
v_map_2220_ = lean_ctor_get(v_opts_2216_, 0);
v___x_2221_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2220_, v_name_2218_);
if (lean_obj_tag(v___x_2221_) == 0)
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_unbox(v_defValue_2219_);
return v___x_2222_;
}
else
{
lean_object* v_val_2223_; 
v_val_2223_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_val_2223_);
lean_dec_ref(v___x_2221_);
if (lean_obj_tag(v_val_2223_) == 1)
{
uint8_t v_v_2224_; 
v_v_2224_ = lean_ctor_get_uint8(v_val_2223_, 0);
lean_dec_ref(v_val_2223_);
return v_v_2224_;
}
else
{
uint8_t v___x_2225_; 
lean_dec(v_val_2223_);
v___x_2225_ = lean_unbox(v_defValue_2219_);
return v___x_2225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2___boxed(lean_object* v_opts_2226_, lean_object* v_opt_2227_){
_start:
{
uint8_t v_res_2228_; lean_object* v_r_2229_; 
v_res_2228_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_opts_2226_, v_opt_2227_);
lean_dec_ref(v_opt_2227_);
lean_dec_ref(v_opts_2226_);
v_r_2229_ = lean_box(v_res_2228_);
return v_r_2229_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__1));
v___x_2234_ = l_Lean_MessageData_ofFormat(v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(lean_object* v_msgData_2235_, lean_object* v_macroStack_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_options_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_options_2239_ = lean_ctor_get(v___y_2237_, 2);
v___x_2240_ = l_Lean_Elab_pp_macroStack;
v___x_2241_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__2(v_options_2239_, v___x_2240_);
if (v___x_2241_ == 0)
{
lean_object* v___x_2242_; 
lean_dec(v_macroStack_2236_);
v___x_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2242_, 0, v_msgData_2235_);
return v___x_2242_;
}
else
{
if (lean_obj_tag(v_macroStack_2236_) == 0)
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v_msgData_2235_);
return v___x_2243_;
}
else
{
lean_object* v_head_2244_; lean_object* v_after_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2260_; 
v_head_2244_ = lean_ctor_get(v_macroStack_2236_, 0);
lean_inc(v_head_2244_);
v_after_2245_ = lean_ctor_get(v_head_2244_, 1);
v_isSharedCheck_2260_ = !lean_is_exclusive(v_head_2244_);
if (v_isSharedCheck_2260_ == 0)
{
lean_object* v_unused_2261_; 
v_unused_2261_ = lean_ctor_get(v_head_2244_, 0);
lean_dec(v_unused_2261_);
v___x_2247_ = v_head_2244_;
v_isShared_2248_ = v_isSharedCheck_2260_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_after_2245_);
lean_dec(v_head_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2260_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3___closed__0);
if (v_isShared_2248_ == 0)
{
lean_ctor_set_tag(v___x_2247_, 7);
lean_ctor_set(v___x_2247_, 1, v___x_2249_);
lean_ctor_set(v___x_2247_, 0, v_msgData_2235_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_msgData_2235_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_msgData_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2252_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___closed__2);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2251_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_MessageData_ofSyntax(v_after_2245_);
v___x_2255_ = l_Lean_indentD(v___x_2254_);
v_msgData_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2256_, 0, v___x_2253_);
lean_ctor_set(v_msgData_2256_, 1, v___x_2255_);
v___x_2257_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1_spec__3(v_msgData_2256_, v_macroStack_2236_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg___boxed(lean_object* v_msgData_2262_, lean_object* v_macroStack_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2262_, v_macroStack_2263_, v___y_2264_);
lean_dec_ref(v___y_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(lean_object* v_msg_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_ref_2275_; lean_object* v___x_2276_; lean_object* v_a_2277_; lean_object* v_macroStack_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2289_; 
v_ref_2275_ = lean_ctor_get(v___y_2272_, 5);
v___x_2276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_2267_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2276_);
v_macroStack_2278_ = lean_ctor_get(v___y_2268_, 1);
v___x_2279_ = l_Lean_Elab_getBetterRef(v_ref_2275_, v_macroStack_2278_);
lean_inc(v_macroStack_2278_);
v___x_2280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_a_2277_, v_macroStack_2278_, v___y_2272_);
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2283_ = v___x_2280_;
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2280_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2289_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2279_);
lean_ctor_set(v___x_2285_, 1, v_a_2281_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 1);
lean_ctor_set(v___x_2283_, 0, v___x_2285_);
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_2299_, lean_object* v___x_2300_, lean_object* v_____r_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2309_, 0, v_a_2299_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2300_);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_2313_, lean_object* v___x_2314_, lean_object* v_____r_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2313_, v___x_2314_, v_____r_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(uint8_t v_cancel_2324_, lean_object* v_fst_2325_, lean_object* v_a_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
if (lean_obj_tag(v_a_2326_) == 0)
{
lean_object* v___x_2335_; 
lean_dec_ref(v_fst_2325_);
v___x_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2335_, 0, v_b_2327_);
return v___x_2335_;
}
else
{
lean_object* v___x_2336_; lean_object* v_fst_2337_; lean_object* v_snd_2338_; lean_object* v___y_2340_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec_ref(v_b_2327_);
v___x_2336_ = l_IO_waitAny_x27___redArg(v_a_2326_);
v_fst_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_fst_2337_);
v_snd_2338_ = lean_ctor_get(v___x_2336_, 1);
lean_inc(v_snd_2338_);
lean_dec_ref(v___x_2336_);
v___x_2360_ = lean_box(0);
lean_inc(v___y_2333_);
lean_inc_ref(v___y_2332_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
v___x_2361_ = lean_apply_7(v_fst_2337_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, lean_box(0));
if (lean_obj_tag(v___x_2361_) == 0)
{
if (v_cancel_2324_ == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref(v___x_2361_);
v___x_2363_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2362_, v___x_2360_, v___x_2360_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
v___y_2340_ = v___x_2363_;
goto v___jp_2339_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_a_2364_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2364_);
lean_dec_ref(v___x_2361_);
lean_inc_ref(v_fst_2325_);
v___x_2365_ = lean_apply_1(v_fst_2325_, lean_box(0));
v___x_2366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___lam__0(v_a_2364_, v___x_2360_, v___x_2365_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
v___y_2340_ = v___x_2366_;
goto v___jp_2339_;
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2380_; 
v_a_2367_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2369_ = v___x_2361_;
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2361_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2380_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; uint8_t v___y_2373_; uint8_t v___x_2378_; 
v___x_2371_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2378_ = l_Lean_Exception_isInterrupt(v_a_2367_);
if (v___x_2378_ == 0)
{
uint8_t v___x_2379_; 
lean_inc(v_a_2367_);
v___x_2379_ = l_Lean_Exception_isRuntime(v_a_2367_);
v___y_2373_ = v___x_2379_;
goto v___jp_2372_;
}
else
{
v___y_2373_ = v___x_2378_;
goto v___jp_2372_;
}
v___jp_2372_:
{
if (v___y_2373_ == 0)
{
lean_del_object(v___x_2369_);
lean_dec(v_a_2367_);
v_a_2326_ = v_snd_2338_;
v_b_2327_ = v___x_2371_;
goto _start;
}
else
{
lean_object* v___x_2376_; 
lean_dec(v_snd_2338_);
lean_dec_ref(v_fst_2325_);
if (v_isShared_2370_ == 0)
{
v___x_2376_ = v___x_2369_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2367_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
v___jp_2339_:
{
if (lean_obj_tag(v___y_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2351_; 
v_a_2341_ = lean_ctor_get(v___y_2340_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___y_2340_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2343_ = v___y_2340_;
v_isShared_2344_ = v_isSharedCheck_2351_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___y_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2351_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
if (lean_obj_tag(v_a_2341_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2347_; 
lean_dec(v_snd_2338_);
lean_dec_ref(v_fst_2325_);
v_a_2345_ = lean_ctor_get(v_a_2341_, 0);
lean_inc(v_a_2345_);
lean_dec_ref(v_a_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_a_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
else
{
lean_object* v_a_2349_; 
lean_del_object(v___x_2343_);
v_a_2349_ = lean_ctor_get(v_a_2341_, 0);
lean_inc(v_a_2349_);
lean_dec_ref(v_a_2341_);
v_a_2326_ = v_snd_2338_;
v_b_2327_ = v_a_2349_;
goto _start;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_snd_2338_);
lean_dec_ref(v_fst_2325_);
v_a_2352_ = lean_ctor_get(v___y_2340_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___y_2340_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___y_2340_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___y_2340_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_2381_, lean_object* v_fst_2382_, lean_object* v_a_2383_, lean_object* v_b_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
uint8_t v_cancel_boxed_2392_; lean_object* v_res_2393_; 
v_cancel_boxed_2392_ = lean_unbox(v_cancel_2381_);
v_res_2393_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_boxed_2392_, v_fst_2382_, v_a_2383_, v_b_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg(lean_object* v_jobs_2394_, uint8_t v_cancel_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Elab_Term_TermElabM_parIterGreedyWithCancel___redArg(v_jobs_2394_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v_fst_2405_; lean_object* v_snd_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2403_);
v_fst_2405_ = lean_ctor_get(v_a_2404_, 0);
lean_inc(v_fst_2405_);
v_snd_2406_ = lean_ctor_get(v_a_2404_, 1);
lean_inc(v_snd_2406_);
lean_dec(v_a_2404_);
v___x_2407_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_2408_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2395_, v_fst_2405_, v_snd_2406_, v___x_2407_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2420_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2420_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v_fst_2413_; 
v_fst_2413_ = lean_ctor_get(v_a_2409_, 0);
lean_inc(v_fst_2413_);
lean_dec(v_a_2409_);
if (lean_obj_tag(v_fst_2413_) == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_del_object(v___x_2411_);
v___x_2414_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_2415_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v___x_2414_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
return v___x_2415_;
}
else
{
lean_object* v_val_2416_; lean_object* v___x_2418_; 
v_val_2416_ = lean_ctor_get(v_fst_2413_, 0);
lean_inc(v_val_2416_);
lean_dec_ref(v_fst_2413_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v_val_2416_);
v___x_2418_ = v___x_2411_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_val_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
v_a_2421_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2408_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2408_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2403_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2403_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___redArg___boxed(lean_object* v_jobs_2437_, lean_object* v_cancel_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
uint8_t v_cancel_boxed_2446_; lean_object* v_res_2447_; 
v_cancel_boxed_2446_ = lean_unbox(v_cancel_2438_);
v_res_2447_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2437_, v_cancel_boxed_2446_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst(lean_object* v_00_u03b1_2448_, lean_object* v_jobs_2449_, uint8_t v_cancel_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_Elab_Term_TermElabM_parFirst___redArg(v_jobs_2449_, v_cancel_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_TermElabM_parFirst___boxed(lean_object* v_00_u03b1_2459_, lean_object* v_jobs_2460_, lean_object* v_cancel_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
uint8_t v_cancel_boxed_2469_; lean_object* v_res_2470_; 
v_cancel_boxed_2469_ = lean_unbox(v_cancel_2461_);
v_res_2470_ = l_Lean_Elab_Term_TermElabM_parFirst(v_00_u03b1_2459_, v_jobs_2460_, v_cancel_boxed_2469_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
lean_dec(v_a_2465_);
lean_dec_ref(v_a_2464_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(lean_object* v_00_u03b1_2471_, uint8_t v_cancel_2472_, lean_object* v_fst_2473_, lean_object* v_inst_2474_, lean_object* v_R_2475_, lean_object* v_a_2476_, lean_object* v_b_2477_, lean_object* v_c_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___redArg(v_cancel_2472_, v_fst_2473_, v_a_2476_, v_b_2477_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0___boxed(lean_object* v_00_u03b1_2487_, lean_object* v_cancel_2488_, lean_object* v_fst_2489_, lean_object* v_inst_2490_, lean_object* v_R_2491_, lean_object* v_a_2492_, lean_object* v_b_2493_, lean_object* v_c_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
uint8_t v_cancel_boxed_2502_; lean_object* v_res_2503_; 
v_cancel_boxed_2502_ = lean_unbox(v_cancel_2488_);
v_res_2503_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Term_TermElabM_parFirst_spec__0(v_00_u03b1_2487_, v_cancel_boxed_2502_, v_fst_2489_, v_inst_2490_, v_R_2491_, v_a_2492_, v_b_2493_, v_c_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(lean_object* v_00_u03b1_2504_, lean_object* v_msg_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___redArg(v_msg_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_2514_, lean_object* v_msg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1(v_00_u03b1_2514_, v_msg_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(lean_object* v_msgData_2524_, lean_object* v_macroStack_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___redArg(v_msgData_2524_, v_macroStack_2525_, v___y_2530_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1___boxed(lean_object* v_msgData_2534_, lean_object* v_macroStack_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_TermElabM_parFirst_spec__1_spec__1(v_msgData_2534_, v_macroStack_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(lean_object* v_x_2544_, lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
if (lean_obj_tag(v_x_2544_) == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = l_List_reverse___redArg(v_x_2545_);
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
return v___x_2556_;
}
else
{
lean_object* v_head_2557_; lean_object* v_tail_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2576_; 
v_head_2557_ = lean_ctor_get(v_x_2544_, 0);
v_tail_2558_ = lean_ctor_get(v_x_2544_, 1);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_x_2544_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2560_ = v_x_2544_;
v_isShared_2561_ = v_isSharedCheck_2576_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_tail_2558_);
lean_inc(v_head_2557_);
lean_dec(v_x_2544_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2576_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Elab_Tactic_TacticM_asTask___redArg(v_head_2557_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref(v___x_2562_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 1, v_x_2545_);
lean_ctor_set(v___x_2560_, 0, v_a_2563_);
v___x_2565_ = v___x_2560_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2563_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_x_2545_);
v___x_2565_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
v_x_2544_ = v_tail_2558_;
v_x_2545_ = v___x_2565_;
goto _start;
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_del_object(v___x_2560_);
lean_dec(v_tail_2558_);
lean_dec(v_x_2545_);
v_a_2568_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2562_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2562_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg___boxed(lean_object* v_x_2577_, lean_object* v_x_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2577_, v_x_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(lean_object* v_jobs_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = lean_box(0);
v___x_2600_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2589_, v___x_2599_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2619_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2619_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v_fst_2606_; lean_object* v_snd_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2618_; 
v___x_2605_ = l_List_unzipTR___redArg(v_a_2601_);
v_fst_2606_ = lean_ctor_get(v___x_2605_, 0);
v_snd_2607_ = lean_ctor_get(v___x_2605_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2609_ = v___x_2605_;
v_isShared_2610_ = v_isSharedCheck_2618_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_snd_2607_);
lean_inc(v_fst_2606_);
lean_dec(v___x_2605_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2618_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2611_, 0, v_fst_2606_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v___x_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_snd_2607_);
v___x_2613_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
lean_object* v___x_2615_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2613_);
v___x_2615_ = v___x_2603_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
v_a_2620_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2600_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2600_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg___boxed(lean_object* v_jobs_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel(lean_object* v_00_u03b1_2639_, lean_object* v_jobs_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterWithCancel___boxed(lean_object* v_00_u03b1_2651_, lean_object* v_jobs_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel(v_00_u03b1_2651_, v_jobs_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(lean_object* v_00_u03b1_2663_, lean_object* v_x_2664_, lean_object* v_x_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_x_2664_, v_x_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___boxed(lean_object* v_00_u03b1_2676_, lean_object* v_x_2677_, lean_object* v_x_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0(v_00_u03b1_2676_, v_x_2677_, v_x_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg(lean_object* v_jobs_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_Elab_Tactic_TacticM_parIterWithCancel___redArg(v_jobs_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2708_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2702_ = v___x_2699_;
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2708_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v_snd_2704_; lean_object* v___x_2706_; 
v_snd_2704_ = lean_ctor_get(v_a_2700_, 1);
lean_inc(v_snd_2704_);
lean_dec(v_a_2700_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v_snd_2704_);
v___x_2706_ = v___x_2702_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_snd_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
v_a_2709_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2699_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2699_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___redArg___boxed(lean_object* v_jobs_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter(lean_object* v_00_u03b1_2728_, lean_object* v_jobs_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Elab_Tactic_TacticM_parIter___redArg(v_jobs_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIter___boxed(lean_object* v_00_u03b1_2740_, lean_object* v_jobs_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_Elab_Tactic_TacticM_parIter(v_00_u03b1_2740_, v_jobs_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(lean_object* v_jobs_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_box(0);
v___x_2763_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_parIterWithCancel_spec__0___redArg(v_jobs_2752_, v___x_2762_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2782_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2782_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2782_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v_fst_2769_; lean_object* v_snd_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2781_; 
v___x_2768_ = l_List_unzipTR___redArg(v_a_2764_);
v_fst_2769_ = lean_ctor_get(v___x_2768_, 0);
v_snd_2770_ = lean_ctor_get(v___x_2768_, 1);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2772_ = v___x_2768_;
v_isShared_2773_ = v_isSharedCheck_2781_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_snd_2770_);
lean_inc(v_fst_2769_);
lean_dec(v___x_2768_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2781_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = lean_alloc_closure((void*)(l_List_forM___at___00Lean_Core_CoreM_parIterWithCancel_spec__1___boxed), 2, 1);
lean_closure_set(v___x_2774_, 0, v_fst_2769_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2774_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_snd_2770_);
v___x_2776_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2776_);
v___x_2778_ = v___x_2766_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
else
{
lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_a_2783_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2763_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2763_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg___boxed(lean_object* v_jobs_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(lean_object* v_00_u03b1_2802_, lean_object* v_jobs_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___boxed(lean_object* v_00_u03b1_2814_, lean_object* v_jobs_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel(v_00_u03b1_2814_, v_jobs_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(lean_object* v_jobs_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2845_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2845_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_snd_2841_; lean_object* v___x_2843_; 
v_snd_2841_ = lean_ctor_get(v_a_2837_, 1);
lean_inc(v_snd_2841_);
lean_dec(v_a_2837_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v_snd_2841_);
v___x_2843_ = v___x_2839_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_snd_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
v_a_2846_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2836_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2836_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg___boxed(lean_object* v_jobs_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
lean_dec(v_a_2858_);
lean_dec_ref(v_a_2857_);
lean_dec(v_a_2856_);
lean_dec_ref(v_a_2855_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy(lean_object* v_00_u03b1_2865_, lean_object* v_jobs_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy___redArg(v_jobs_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parIterGreedy___boxed(lean_object* v_00_u03b1_2877_, lean_object* v_jobs_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_Elab_Tactic_TacticM_parIterGreedy(v_00_u03b1_2877_, v_jobs_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(lean_object* v_as_x27_2889_, lean_object* v_b_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
if (lean_obj_tag(v_as_x27_2889_) == 0)
{
lean_object* v___x_2900_; 
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v_b_2890_);
return v___x_2900_;
}
else
{
lean_object* v_head_2901_; lean_object* v_tail_2902_; lean_object* v___x_2903_; 
v_head_2901_ = lean_ctor_get(v_as_x27_2889_, 0);
v_tail_2902_ = lean_ctor_get(v_as_x27_2889_, 1);
v___x_2903_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2892_, v___y_2894_, v___y_2896_, v___y_2898_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2947_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2947_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2947_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___y_2909_; uint8_t v___y_2910_; lean_object* v_a_2927_; lean_object* v___x_2645__overap_2930_; lean_object* v___x_2931_; 
lean_inc(v_head_2901_);
v___x_2645__overap_2930_ = lean_task_get_own(v_head_2901_);
lean_inc(v___y_2898_);
lean_inc_ref(v___y_2897_);
lean_inc(v___y_2896_);
lean_inc_ref(v___y_2895_);
lean_inc(v___y_2894_);
lean_inc_ref(v___y_2893_);
lean_inc(v___y_2892_);
lean_inc_ref(v___y_2891_);
v___x_2931_ = lean_apply_9(v___x_2645__overap_2930_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, lean_box(0));
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_2892_, v___y_2894_, v___y_2896_, v___y_2898_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2944_; 
lean_del_object(v___x_2906_);
lean_dec(v_a_2904_);
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_2944_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2944_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v_a_2932_);
lean_ctor_set(v___x_2938_, 1, v_a_2934_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set_tag(v___x_2936_, 1);
lean_ctor_set(v___x_2936_, 0, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v_b_2890_);
v_as_x27_2889_ = v_tail_2902_;
v_b_2890_ = v___x_2941_;
goto _start;
}
}
}
else
{
lean_object* v_a_2945_; 
lean_dec(v_a_2932_);
v_a_2945_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2933_);
v_a_2927_ = v_a_2945_;
goto v___jp_2926_;
}
}
else
{
lean_object* v_a_2946_; 
v_a_2946_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2931_);
v_a_2927_ = v_a_2946_;
goto v___jp_2926_;
}
v___jp_2908_:
{
if (v___y_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_del_object(v___x_2906_);
v___x_2911_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_2904_, v___y_2910_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec_ref(v___x_2911_);
v___x_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2912_, 0, v___y_2909_);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v_b_2890_);
v_as_x27_2889_ = v_tail_2902_;
v_b_2890_ = v___x_2913_;
goto _start;
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v___y_2909_);
lean_dec(v_b_2890_);
v_a_2915_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2911_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2911_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_object* v___x_2924_; 
lean_dec(v_a_2904_);
lean_dec(v_b_2890_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set_tag(v___x_2906_, 1);
lean_ctor_set(v___x_2906_, 0, v___y_2909_);
v___x_2924_ = v___x_2906_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___y_2909_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
v___jp_2926_:
{
uint8_t v___x_2928_; 
v___x_2928_ = l_Lean_Exception_isInterrupt(v_a_2927_);
if (v___x_2928_ == 0)
{
uint8_t v___x_2929_; 
lean_inc_ref(v_a_2927_);
v___x_2929_ = l_Lean_Exception_isRuntime(v_a_2927_);
v___y_2909_ = v_a_2927_;
v___y_2910_ = v___x_2929_;
goto v___jp_2908_;
}
else
{
v___y_2909_ = v_a_2927_;
v___y_2910_ = v___x_2928_;
goto v___jp_2908_;
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec(v_b_2890_);
v_a_2948_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2903_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2903_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg___boxed(lean_object* v_as_x27_2956_, lean_object* v_b_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_2956_, v_b_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v_as_x27_2956_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(lean_object* v_x_2968_, lean_object* v_x_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
if (lean_obj_tag(v_x_2968_) == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2979_ = l_List_reverse___redArg(v_x_2969_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
return v___x_2980_;
}
else
{
lean_object* v_head_2981_; lean_object* v_tail_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3000_; 
v_head_2981_ = lean_ctor_get(v_x_2968_, 0);
v_tail_2982_ = lean_ctor_get(v_x_2968_, 1);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_x_2968_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2984_ = v_x_2968_;
v_isShared_2985_ = v_isSharedCheck_3000_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_tail_2982_);
lean_inc(v_head_2981_);
lean_dec(v_x_2968_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3000_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; 
v___x_2986_ = l_Lean_Elab_Tactic_TacticM_asTask_x27___redArg(v_head_2981_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2989_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref(v___x_2986_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 1, v_x_2969_);
lean_ctor_set(v___x_2984_, 0, v_a_2987_);
v___x_2989_ = v___x_2984_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2987_);
lean_ctor_set(v_reuseFailAlloc_2991_, 1, v_x_2969_);
v___x_2989_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
v_x_2968_ = v_tail_2982_;
v_x_2969_ = v___x_2989_;
goto _start;
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_del_object(v___x_2984_);
lean_dec(v_tail_2982_);
lean_dec(v_x_2969_);
v_a_2992_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2986_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2986_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg___boxed(lean_object* v_x_3001_, lean_object* v_x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3001_, v_x_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg(lean_object* v_jobs_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = lean_st_ref_get(v_a_3015_);
v___x_3024_ = lean_box(0);
v___x_3025_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_jobs_3013_, v___x_3024_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_a_3026_, v___x_3024_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_);
lean_dec(v_a_3026_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3037_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3037_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3037_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3032_ = lean_st_ref_set(v_a_3015_, v___x_3023_);
v___x_3033_ = l_List_reverse___redArg(v_a_3028_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 0, v___x_3033_);
v___x_3035_ = v___x_3030_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
else
{
lean_dec(v___x_3023_);
return v___x_3027_;
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec(v___x_3023_);
v_a_3038_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3025_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3025_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___redArg___boxed(lean_object* v_jobs_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par(lean_object* v_00_u03b1_3057_, lean_object* v_jobs_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_Elab_Tactic_TacticM_par___redArg(v_jobs_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par___boxed(lean_object* v_00_u03b1_3069_, lean_object* v_jobs_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_Elab_Tactic_TacticM_par(v_00_u03b1_3069_, v_jobs_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(lean_object* v_00_u03b1_3081_, lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_x_3082_, v_x_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___boxed(lean_object* v_00_u03b1_3094_, lean_object* v_x_3095_, lean_object* v_x_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0(v_00_u03b1_3094_, v_x_3095_, v_x_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(lean_object* v_00_u03b1_3107_, lean_object* v_as_3108_, lean_object* v_as_x27_3109_, lean_object* v_b_3110_, lean_object* v_a_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___redArg(v_as_x27_3109_, v_b_3110_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1___boxed(lean_object* v_00_u03b1_3122_, lean_object* v_as_3123_, lean_object* v_as_x27_3124_, lean_object* v_b_3125_, lean_object* v_a_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__1(v_00_u03b1_3122_, v_as_3123_, v_as_x27_3124_, v_b_3125_, v_a_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v_as_x27_3124_);
lean_dec(v_as_3123_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(lean_object* v_as_x27_3137_, lean_object* v_b_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
if (lean_obj_tag(v_as_x27_3137_) == 0)
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3148_, 0, v_b_3138_);
return v___x_3148_;
}
else
{
lean_object* v_head_3149_; lean_object* v_tail_3150_; lean_object* v___x_3151_; 
v_head_3149_ = lean_ctor_get(v_as_x27_3137_, 0);
v_tail_3150_ = lean_ctor_get(v_as_x27_3137_, 1);
v___x_3151_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3140_, v___y_3142_, v___y_3144_, v___y_3146_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_2330__overap_3153_; lean_object* v___x_3154_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref(v___x_3151_);
lean_inc(v_head_3149_);
v___x_2330__overap_3153_ = lean_task_get_own(v_head_3149_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
lean_inc(v___y_3144_);
lean_inc_ref(v___y_3143_);
lean_inc(v___y_3142_);
lean_inc_ref(v___y_3141_);
lean_inc(v___y_3140_);
lean_inc_ref(v___y_3139_);
v___x_3154_ = lean_apply_9(v___x_2330__overap_3153_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, lean_box(0));
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec(v_a_3152_);
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v_a_3155_);
v___x_3157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
lean_ctor_set(v___x_3157_, 1, v_b_3138_);
v_as_x27_3137_ = v_tail_3150_;
v_b_3138_ = v___x_3157_;
goto _start;
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3182_; 
v_a_3159_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3161_ = v___x_3154_;
v_isShared_3162_ = v_isSharedCheck_3182_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3154_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3182_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
uint8_t v___y_3164_; uint8_t v___x_3180_; 
v___x_3180_ = l_Lean_Exception_isInterrupt(v_a_3159_);
if (v___x_3180_ == 0)
{
uint8_t v___x_3181_; 
lean_inc(v_a_3159_);
v___x_3181_ = l_Lean_Exception_isRuntime(v_a_3159_);
v___y_3164_ = v___x_3181_;
goto v___jp_3163_;
}
else
{
v___y_3164_ = v___x_3180_;
goto v___jp_3163_;
}
v___jp_3163_:
{
if (v___y_3164_ == 0)
{
lean_object* v___x_3165_; 
lean_del_object(v___x_3161_);
v___x_3165_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3152_, v___y_3164_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
lean_dec_ref(v___x_3165_);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_a_3159_);
v___x_3167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3166_);
lean_ctor_set(v___x_3167_, 1, v_b_3138_);
v_as_x27_3137_ = v_tail_3150_;
v_b_3138_ = v___x_3167_;
goto _start;
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_a_3159_);
lean_dec(v_b_3138_);
v_a_3169_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3165_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3165_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v___x_3178_; 
lean_dec(v_a_3152_);
lean_dec(v_b_3138_);
if (v_isShared_3162_ == 0)
{
v___x_3178_ = v___x_3161_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3159_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_dec(v_b_3138_);
v_a_3183_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3151_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3151_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg___boxed(lean_object* v_as_x27_3191_, lean_object* v_b_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_as_x27_3191_, v_b_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v_as_x27_3191_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg(lean_object* v_jobs_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_st_ref_get(v_a_3205_);
v___x_3214_ = lean_box(0);
v___x_3215_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_TacticM_par_spec__0___redArg(v_jobs_3203_, v___x_3214_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref(v___x_3215_);
v___x_3217_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_a_3216_, v___x_3214_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_);
lean_dec(v_a_3216_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3227_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3227_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3227_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3222_ = lean_st_ref_set(v_a_3205_, v___x_3213_);
v___x_3223_ = l_List_reverse___redArg(v_a_3218_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v___x_3223_);
v___x_3225_ = v___x_3220_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
else
{
lean_dec(v___x_3213_);
return v___x_3217_;
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v___x_3213_);
v_a_3228_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3215_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3215_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___redArg___boxed(lean_object* v_jobs_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(v_jobs_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
lean_dec(v_a_3244_);
lean_dec_ref(v_a_3243_);
lean_dec(v_a_3242_);
lean_dec_ref(v_a_3241_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27(lean_object* v_00_u03b1_3247_, lean_object* v_jobs_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_Elab_Tactic_TacticM_par_x27___redArg(v_jobs_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_par_x27___boxed(lean_object* v_00_u03b1_3259_, lean_object* v_jobs_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_){
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Elab_Tactic_TacticM_par_x27(v_00_u03b1_3259_, v_jobs_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(lean_object* v_00_u03b1_3271_, lean_object* v_as_3272_, lean_object* v_as_x27_3273_, lean_object* v_b_3274_, lean_object* v_a_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___redArg(v_as_x27_3273_, v_b_3274_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0___boxed(lean_object* v_00_u03b1_3286_, lean_object* v_as_3287_, lean_object* v_as_x27_3288_, lean_object* v_b_3289_, lean_object* v_a_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_TacticM_par_x27_spec__0(v_00_u03b1_3286_, v_as_3287_, v_as_x27_3288_, v_b_3289_, v_a_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___y_3295_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v_as_x27_3288_);
lean_dec(v_as_3287_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(lean_object* v_a_3301_, lean_object* v___x_3302_, lean_object* v_____r_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v_a_3301_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v___x_3302_);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0___boxed(lean_object* v_a_3317_, lean_object* v___x_3318_, lean_object* v_____r_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3317_, v___x_3318_, v_____r_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(uint8_t v_cancel_3330_, lean_object* v_fst_3331_, lean_object* v_a_3332_, lean_object* v_b_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
if (lean_obj_tag(v_a_3332_) == 0)
{
lean_object* v___x_3343_; 
lean_dec_ref(v_fst_3331_);
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_b_3333_);
return v___x_3343_;
}
else
{
lean_object* v___x_3344_; lean_object* v_fst_3345_; lean_object* v_snd_3346_; lean_object* v___y_3348_; lean_object* v___x_3368_; 
lean_dec_ref(v_b_3333_);
v___x_3344_ = l_IO_waitAny_x27___redArg(v_a_3332_);
v_fst_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_fst_3345_);
v_snd_3346_ = lean_ctor_get(v___x_3344_, 1);
lean_inc(v_snd_3346_);
lean_dec_ref(v___x_3344_);
v___x_3368_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_3335_, v___y_3337_, v___y_3339_, v___y_3341_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref(v___x_3368_);
v___x_3370_ = lean_box(0);
lean_inc(v___y_3341_);
lean_inc_ref(v___y_3340_);
lean_inc(v___y_3339_);
lean_inc_ref(v___y_3338_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
v___x_3371_ = lean_apply_9(v_fst_3345_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, lean_box(0));
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_dec(v_a_3369_);
if (v_cancel_3330_ == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref(v___x_3371_);
v___x_3373_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3372_, v___x_3370_, v___x_3370_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
v___y_3348_ = v___x_3373_;
goto v___jp_3347_;
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_a_3374_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3374_);
lean_dec_ref(v___x_3371_);
lean_inc_ref(v_fst_3331_);
v___x_3375_ = lean_apply_1(v_fst_3331_, lean_box(0));
v___x_3376_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___lam__0(v_a_3374_, v___x_3370_, v___x_3375_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
v___y_3348_ = v___x_3376_;
goto v___jp_3347_;
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3399_; 
v_a_3377_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3379_ = v___x_3371_;
v_isShared_3380_ = v_isSharedCheck_3399_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3371_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3399_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; uint8_t v___y_3383_; uint8_t v___x_3397_; 
v___x_3381_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_3397_ = l_Lean_Exception_isInterrupt(v_a_3377_);
if (v___x_3397_ == 0)
{
uint8_t v___x_3398_; 
lean_inc(v_a_3377_);
v___x_3398_ = l_Lean_Exception_isRuntime(v_a_3377_);
v___y_3383_ = v___x_3398_;
goto v___jp_3382_;
}
else
{
v___y_3383_ = v___x_3397_;
goto v___jp_3382_;
}
v___jp_3382_:
{
if (v___y_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_del_object(v___x_3379_);
lean_dec(v_a_3377_);
v___x_3384_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(v_a_3369_, v___y_3383_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_dec_ref(v___x_3384_);
v_a_3332_ = v_snd_3346_;
v_b_3333_ = v___x_3381_;
goto _start;
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec(v_snd_3346_);
lean_dec_ref(v_fst_3331_);
v_a_3386_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3384_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3384_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v___x_3395_; 
lean_dec(v_a_3369_);
lean_dec(v_snd_3346_);
lean_dec_ref(v_fst_3331_);
if (v_isShared_3380_ == 0)
{
v___x_3395_ = v___x_3379_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3377_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_snd_3346_);
lean_dec(v_fst_3345_);
lean_dec_ref(v_fst_3331_);
v_a_3400_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3368_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3368_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
v___jp_3347_:
{
if (lean_obj_tag(v___y_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3359_; 
v_a_3349_ = lean_ctor_get(v___y_3348_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___y_3348_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3351_ = v___y_3348_;
v_isShared_3352_ = v_isSharedCheck_3359_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___y_3348_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3359_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
if (lean_obj_tag(v_a_3349_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; 
lean_dec(v_snd_3346_);
lean_dec_ref(v_fst_3331_);
v_a_3353_ = lean_ctor_get(v_a_3349_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v_a_3349_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v_a_3353_);
v___x_3355_ = v___x_3351_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
else
{
lean_object* v_a_3357_; 
lean_del_object(v___x_3351_);
v_a_3357_ = lean_ctor_get(v_a_3349_, 0);
lean_inc(v_a_3357_);
lean_dec_ref(v_a_3349_);
v_a_3332_ = v_snd_3346_;
v_b_3333_ = v_a_3357_;
goto _start;
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_dec(v_snd_3346_);
lean_dec_ref(v_fst_3331_);
v_a_3360_ = lean_ctor_get(v___y_3348_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___y_3348_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___y_3348_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___y_3348_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg___boxed(lean_object* v_cancel_3408_, lean_object* v_fst_3409_, lean_object* v_a_3410_, lean_object* v_b_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v_cancel_boxed_3421_; lean_object* v_res_3422_; 
v_cancel_boxed_3421_ = lean_unbox(v_cancel_3408_);
v_res_3422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_boxed_3421_, v_fst_3409_, v_a_3410_, v_b_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(lean_object* v_msg_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_ref_3429_; lean_object* v___x_3430_; lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3439_; 
v_ref_3429_ = lean_ctor_get(v___y_3426_, 5);
v___x_3430_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_MetaM_parFirst_spec__1_spec__1(v_msg_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
lean_inc(v_ref_3429_);
v___x_3435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3435_, 0, v_ref_3429_);
lean_ctor_set(v___x_3435_, 1, v_a_3431_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set_tag(v___x_3433_, 1);
lean_ctor_set(v___x_3433_, 0, v___x_3435_);
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg___boxed(lean_object* v_msg_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v_res_3446_; 
v_res_3446_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg(lean_object* v_jobs_3447_, uint8_t v_cancel_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_Elab_Tactic_TacticM_parIterGreedyWithCancel___redArg(v_jobs_3447_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v_fst_3460_; lean_object* v_snd_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref(v___x_3458_);
v_fst_3460_ = lean_ctor_get(v_a_3459_, 0);
lean_inc(v_fst_3460_);
v_snd_3461_ = lean_ctor_get(v_a_3459_, 1);
lean_inc(v_snd_3461_);
lean_dec(v_a_3459_);
v___x_3462_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Core_CoreM_parFirst_spec__0___redArg___closed__0));
v___x_3463_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3448_, v_fst_3460_, v_snd_3461_, v___x_3462_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3475_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3475_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3475_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v_fst_3468_; 
v_fst_3468_ = lean_ctor_get(v_a_3464_, 0);
lean_inc(v_fst_3468_);
lean_dec(v_a_3464_);
if (lean_obj_tag(v_fst_3468_) == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_del_object(v___x_3466_);
v___x_3469_ = lean_obj_once(&l_Lean_Core_CoreM_parFirst___redArg___closed__1, &l_Lean_Core_CoreM_parFirst___redArg___closed__1_once, _init_l_Lean_Core_CoreM_parFirst___redArg___closed__1);
v___x_3470_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v___x_3469_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
return v___x_3470_;
}
else
{
lean_object* v_val_3471_; lean_object* v___x_3473_; 
v_val_3471_ = lean_ctor_get(v_fst_3468_, 0);
lean_inc(v_val_3471_);
lean_dec_ref(v_fst_3468_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v_val_3471_);
v___x_3473_ = v___x_3466_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_val_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
v_a_3476_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3463_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3463_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_a_3484_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3458_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3458_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___redArg___boxed(lean_object* v_jobs_3492_, lean_object* v_cancel_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
uint8_t v_cancel_boxed_3503_; lean_object* v_res_3504_; 
v_cancel_boxed_3503_ = lean_unbox(v_cancel_3493_);
v_res_3504_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3492_, v_cancel_boxed_3503_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_);
lean_dec(v_a_3501_);
lean_dec_ref(v_a_3500_);
lean_dec(v_a_3499_);
lean_dec_ref(v_a_3498_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst(lean_object* v_00_u03b1_3505_, lean_object* v_jobs_3506_, uint8_t v_cancel_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v___x_3517_; 
v___x_3517_ = l_Lean_Elab_Tactic_TacticM_parFirst___redArg(v_jobs_3506_, v_cancel_3507_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_TacticM_parFirst___boxed(lean_object* v_00_u03b1_3518_, lean_object* v_jobs_3519_, lean_object* v_cancel_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
uint8_t v_cancel_boxed_3530_; lean_object* v_res_3531_; 
v_cancel_boxed_3530_ = lean_unbox(v_cancel_3520_);
v_res_3531_ = l_Lean_Elab_Tactic_TacticM_parFirst(v_00_u03b1_3518_, v_jobs_3519_, v_cancel_boxed_3530_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(lean_object* v_00_u03b1_3532_, uint8_t v_cancel_3533_, lean_object* v_fst_3534_, lean_object* v_inst_3535_, lean_object* v_R_3536_, lean_object* v_a_3537_, lean_object* v_b_3538_, lean_object* v_c_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___redArg(v_cancel_3533_, v_fst_3534_, v_a_3537_, v_b_3538_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_3550_ = _args[0];
lean_object* v_cancel_3551_ = _args[1];
lean_object* v_fst_3552_ = _args[2];
lean_object* v_inst_3553_ = _args[3];
lean_object* v_R_3554_ = _args[4];
lean_object* v_a_3555_ = _args[5];
lean_object* v_b_3556_ = _args[6];
lean_object* v_c_3557_ = _args[7];
lean_object* v___y_3558_ = _args[8];
lean_object* v___y_3559_ = _args[9];
lean_object* v___y_3560_ = _args[10];
lean_object* v___y_3561_ = _args[11];
lean_object* v___y_3562_ = _args[12];
lean_object* v___y_3563_ = _args[13];
lean_object* v___y_3564_ = _args[14];
lean_object* v___y_3565_ = _args[15];
lean_object* v___y_3566_ = _args[16];
_start:
{
uint8_t v_cancel_boxed_3567_; lean_object* v_res_3568_; 
v_cancel_boxed_3567_ = lean_unbox(v_cancel_3551_);
v_res_3568_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__0(v_00_u03b1_3550_, v_cancel_boxed_3567_, v_fst_3552_, v_inst_3553_, v_R_3554_, v_a_3555_, v_b_3556_, v_c_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(lean_object* v_00_u03b1_3569_, lean_object* v_msg_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___redArg(v_msg_3570_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1___boxed(lean_object* v_00_u03b1_3581_, lean_object* v_msg_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_throwError___at___00Lean_Elab_Tactic_TacticM_parFirst_spec__1(v_00_u03b1_3581_, v_msg_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec_ref(v___y_3585_);
lean_dec(v___y_3584_);
lean_dec_ref(v___y_3583_);
return v_res_3592_;
}
}
lean_object* runtime_initialize_Lean_Elab_Task(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Parallel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
