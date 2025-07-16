// Lean compiler output
// Module: Lake.Build.Job.Monad
// Imports: Lake.Build.Fetch
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectList(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftJobMFetchM;
lean_object* l_Substring_takeRightWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mk___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mk(lean_object*, lean_object*);
static lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__1;
LEAN_EXPORT lean_object* l_Lake_Job_bindSync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__3;
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildJob_mixList___redArg___closed__0;
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_ofJob___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_collectList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mapWithTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray___redArg___boxed(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lake_instMonadStateOfLogJobM___closed__0;
static lean_object* l_Lake_takeTrace___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mapWithTrace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob___redArg___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadLiftSpawnMJobM___closed__0;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM;
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_collectList_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindSync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_ofJob(lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_wait_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_withIsolatedStreams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_instFunctor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_BuildJob_nil___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instDataKindUnit;
static lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__2;
static lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__4;
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_instPure;
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildJob_nil___closed__2;
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_instFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray___redArg___boxed(lean_object*);
static lean_object* l_Lake_Job_async___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_pure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_map___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mapWithTrace___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_instPure___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadLiftFetchMJobM___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_add___redArg(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__7;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Job_async___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM;
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM;
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftSpawnMJobM;
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Job_async___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_pure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildJob_nil___closed__1;
LEAN_EXPORT lean_object* l_Lake_instMonadLiftFetchMJobM;
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_mixList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_takeTrace___redArg___closed__1;
lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_instFunctor;
static lean_object* l_Lake_Job_async___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mk___redArg(lean_object*);
static lean_object* l_Lake_instMonadLiftJobMFetchM___closed__0;
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_mixList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLogJobM;
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_pushLogEntry(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* l_Function_const___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_wait_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildJob_nil;
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_EquipT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_tryFinally___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instMonadLogJobM___closed__0;
static lean_object* l_Lake_Job_zipResultWith___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfJobStateJobM;
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadStateOfJobStateJobM___closed__0;
x_2 = l_Lake_EStateT_instMonadStateOfOfPure___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_instMonadStateOfJobStateJobM___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = l_Lake_instMonadStateOfJobStateJobM___closed__2;
x_7 = l_Lake_instMonadStateOfJobStateJobM___closed__3;
x_8 = l_Lake_instMonadStateOfJobStateJobM___closed__4;
x_9 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_7);
x_10 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_3);
x_12 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_8);
x_13 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_8);
x_14 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, lean_box(0));
lean_closure_set(x_14, 3, lean_box(0));
lean_closure_set(x_14, 4, x_11);
x_15 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_7);
x_16 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_7);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_17, 0, lean_box(0));
lean_closure_set(x_17, 1, x_14);
x_18 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_7);
x_19 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_7);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_17);
x_21 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_21, 0, x_18);
lean_closure_set(x_21, 1, x_6);
x_22 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_6);
x_23 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_23, 0, lean_box(0));
lean_closure_set(x_23, 1, lean_box(0));
lean_closure_set(x_23, 2, lean_box(0));
lean_closure_set(x_23, 3, x_20);
lean_ctor_set(x_1, 2, x_22);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_27 = l_Lake_instMonadStateOfJobStateJobM___closed__2;
x_28 = l_Lake_instMonadStateOfJobStateJobM___closed__3;
x_29 = l_Lake_instMonadStateOfJobStateJobM___closed__4;
x_30 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_30, 0, x_25);
lean_closure_set(x_30, 1, x_28);
x_31 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_31, 0, x_26);
lean_closure_set(x_31, 1, x_28);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, x_24);
x_33 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_33, 0, x_30);
lean_closure_set(x_33, 1, x_29);
x_34 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_34, 0, x_31);
lean_closure_set(x_34, 1, x_29);
x_35 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(x_35, 0, lean_box(0));
lean_closure_set(x_35, 1, lean_box(0));
lean_closure_set(x_35, 2, lean_box(0));
lean_closure_set(x_35, 3, lean_box(0));
lean_closure_set(x_35, 4, x_32);
x_36 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_36, 0, x_33);
lean_closure_set(x_36, 1, x_28);
x_37 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_37, 0, x_34);
lean_closure_set(x_37, 1, x_28);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_38, 0, lean_box(0));
lean_closure_set(x_38, 1, x_35);
x_39 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_39, 0, x_36);
lean_closure_set(x_39, 1, x_28);
x_40 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_40, 0, x_37);
lean_closure_set(x_40, 1, x_28);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, x_38);
x_42 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_42, 0, x_39);
lean_closure_set(x_42, 1, x_27);
x_43 = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(x_43, 0, x_40);
lean_closure_set(x_43, 1, x_27);
x_44 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_44, 0, lean_box(0));
lean_closure_set(x_44, 1, lean_box(0));
lean_closure_set(x_44, 2, lean_box(0));
lean_closure_set(x_44, 3, x_41);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_43);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_apply_1(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_8, 0, x_14);
lean_ctor_set(x_12, 1, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_8);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_20);
lean_dec(x_8);
x_23 = lean_apply_1(x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_21);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
return x_29;
}
}
}
static lean_object* _init_l_Lake_instMonadStateOfLogJobM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadStateOfLogJobM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_5);
lean_inc(x_5);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_5);
lean_inc_ref(x_11);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_7);
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_5);
x_15 = l_Lake_EStateT_instFunctor___redArg(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_16, 0, x_7);
lean_ctor_set(x_3, 4, x_12);
lean_ctor_set(x_3, 3, x_13);
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_11);
x_17 = l_ReaderT_instMonad___redArg(x_1);
x_18 = l_ReaderT_instMonad___redArg(x_17);
x_19 = l_ReaderT_instMonad___redArg(x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__0___boxed), 1, 0);
x_25 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__1___boxed), 6, 0);
x_26 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__2___boxed), 8, 0);
x_27 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__3___boxed), 9, 0);
lean_inc_ref(x_23);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_28, 0, x_23);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_23);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, lean_box(0));
lean_closure_set(x_30, 3, x_25);
x_31 = lean_alloc_closure((void*)(l_Lake_EquipT_map), 8, 7);
lean_closure_set(x_31, 0, lean_box(0));
lean_closure_set(x_31, 1, lean_box(0));
lean_closure_set(x_31, 2, x_19);
lean_closure_set(x_31, 3, lean_box(0));
lean_closure_set(x_31, 4, lean_box(0));
lean_closure_set(x_31, 5, x_24);
lean_closure_set(x_31, 6, x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_ctor_get(x_33, 0);
lean_inc_ref(x_34);
lean_dec_ref(x_33);
x_35 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__0___boxed), 1, 0);
x_36 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__1___boxed), 6, 0);
x_37 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__2___boxed), 8, 0);
x_38 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__3___boxed), 9, 0);
lean_inc_ref(x_34);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_34);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_42, 0, lean_box(0));
lean_closure_set(x_42, 1, lean_box(0));
lean_closure_set(x_42, 2, lean_box(0));
lean_closure_set(x_42, 3, x_36);
x_43 = lean_alloc_closure((void*)(l_Lake_EquipT_map), 8, 7);
lean_closure_set(x_43, 0, lean_box(0));
lean_closure_set(x_43, 1, lean_box(0));
lean_closure_set(x_43, 2, x_41);
lean_closure_set(x_43, 3, lean_box(0));
lean_closure_set(x_43, 4, lean_box(0));
lean_closure_set(x_43, 5, x_35);
lean_closure_set(x_43, 6, x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_38);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
lean_inc(x_45);
lean_inc(x_47);
x_48 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_48, 0, x_47);
lean_closure_set(x_48, 1, x_45);
lean_inc(x_45);
lean_inc(x_47);
x_49 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_49, 0, x_47);
lean_closure_set(x_49, 1, x_45);
lean_inc_ref(x_48);
lean_inc(x_47);
x_50 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_50, 0, x_47);
lean_closure_set(x_50, 1, x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
x_51 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_51, 0, x_46);
lean_closure_set(x_51, 1, x_47);
lean_closure_set(x_51, 2, x_45);
x_52 = l_Lake_EStateT_instFunctor___redArg(x_46);
x_53 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_53, 0, x_47);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_54, 4, x_49);
lean_ctor_set(x_1, 1, x_48);
lean_ctor_set(x_1, 0, x_54);
x_55 = l_ReaderT_instMonad___redArg(x_1);
x_56 = l_ReaderT_instMonad___redArg(x_55);
x_57 = l_ReaderT_instMonad___redArg(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_60);
lean_dec_ref(x_58);
x_61 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__0___boxed), 1, 0);
x_62 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__1___boxed), 6, 0);
x_63 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__2___boxed), 8, 0);
x_64 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__3___boxed), 9, 0);
lean_inc_ref(x_60);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_65, 0, x_60);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_66, 0, x_60);
if (lean_is_scalar(x_59)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_59;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_68, 0, lean_box(0));
lean_closure_set(x_68, 1, lean_box(0));
lean_closure_set(x_68, 2, lean_box(0));
lean_closure_set(x_68, 3, x_62);
x_69 = lean_alloc_closure((void*)(l_Lake_EquipT_map), 8, 7);
lean_closure_set(x_69, 0, lean_box(0));
lean_closure_set(x_69, 1, lean_box(0));
lean_closure_set(x_69, 2, x_67);
lean_closure_set(x_69, 3, lean_box(0));
lean_closure_set(x_69, 4, lean_box(0));
lean_closure_set(x_69, 5, x_61);
lean_closure_set(x_69, 6, x_68);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
lean_ctor_set(x_70, 2, x_64);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_71 = lean_ctor_get(x_1, 0);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_1);
x_73 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
lean_inc(x_72);
lean_inc(x_74);
x_76 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_76, 0, x_74);
lean_closure_set(x_76, 1, x_72);
lean_inc(x_72);
lean_inc(x_74);
x_77 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_77, 0, x_74);
lean_closure_set(x_77, 1, x_72);
lean_inc_ref(x_76);
lean_inc(x_74);
x_78 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_78, 0, x_74);
lean_closure_set(x_78, 1, x_76);
lean_inc(x_74);
lean_inc_ref(x_73);
x_79 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_79, 0, x_73);
lean_closure_set(x_79, 1, x_74);
lean_closure_set(x_79, 2, x_72);
x_80 = l_Lake_EStateT_instFunctor___redArg(x_73);
x_81 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_81, 0, x_74);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 5, 0);
} else {
 x_82 = x_75;
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_77);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
x_84 = l_ReaderT_instMonad___redArg(x_83);
x_85 = l_ReaderT_instMonad___redArg(x_84);
x_86 = l_ReaderT_instMonad___redArg(x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_89);
lean_dec_ref(x_87);
x_90 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__0___boxed), 1, 0);
x_91 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__1___boxed), 6, 0);
x_92 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__2___boxed), 8, 0);
x_93 = lean_alloc_closure((void*)(l_Lake_instMonadStateOfLogJobM___lam__3___boxed), 9, 0);
lean_inc_ref(x_89);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_94, 0, x_89);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_95, 0, x_89);
if (lean_is_scalar(x_88)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_88;
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(x_97, 0, lean_box(0));
lean_closure_set(x_97, 1, lean_box(0));
lean_closure_set(x_97, 2, lean_box(0));
lean_closure_set(x_97, 3, x_91);
x_98 = lean_alloc_closure((void*)(l_Lake_EquipT_map), 8, 7);
lean_closure_set(x_98, 0, lean_box(0));
lean_closure_set(x_98, 1, lean_box(0));
lean_closure_set(x_98, 2, x_96);
lean_closure_set(x_98, 3, lean_box(0));
lean_closure_set(x_98, 4, lean_box(0));
lean_closure_set(x_98, 5, x_90);
lean_closure_set(x_98, 6, x_97);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
lean_ctor_set(x_99, 2, x_93);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instMonadStateOfLogJobM___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_instMonadStateOfLogJobM___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_instMonadStateOfLogJobM___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_instMonadStateOfLogJobM___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lake_instMonadLogJobM___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadStateOfLogJobM;
x_2 = lean_alloc_closure((void*)(l_Lake_pushLogEntry), 3, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instMonadLogJobM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instMonadLogJobM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = 3;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = lean_array_get_size(x_11);
x_15 = lean_array_push(x_11, x_13);
lean_ctor_set(x_8, 0, x_15);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_8);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_18);
x_24 = lean_array_push(x_18, x_22);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
}
static lean_object* _init_l_Lake_instMonadErrorJobM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadErrorJobM___lam__0___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_instMonadErrorJobM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_array_get_size(x_9);
lean_dec_ref(x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_apply_7(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_12);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = l_Array_shrink___redArg(x_17, x_15);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_apply_8(x_3, x_19, x_4, x_5, x_6, x_7, x_8, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_21);
lean_dec(x_13);
x_24 = l_Array_shrink___redArg(x_21, x_15);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_22);
x_26 = lean_box(0);
x_27 = lean_apply_8(x_3, x_26, x_4, x_5, x_6, x_7, x_8, x_25, x_14);
return x_27;
}
}
}
}
static lean_object* _init_l_Lake_instAlternativeJobM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 4);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 3);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_11, 0, x_7);
lean_closure_set(x_11, 1, x_5);
lean_inc(x_5);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_5);
lean_inc_ref(x_11);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_13, 0, x_7);
lean_closure_set(x_13, 1, x_11);
lean_inc(x_7);
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_14, 0, x_6);
lean_closure_set(x_14, 1, x_7);
lean_closure_set(x_14, 2, x_5);
x_15 = l_Lake_EStateT_instFunctor___redArg(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_16, 0, x_7);
lean_ctor_set(x_3, 4, x_12);
lean_ctor_set(x_3, 3, x_13);
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_1, 1, x_11);
x_17 = l_ReaderT_instMonad___redArg(x_1);
x_18 = l_ReaderT_instMonad___redArg(x_17);
x_19 = l_ReaderT_instMonad___redArg(x_18);
x_20 = l_ReaderT_instMonad___redArg(x_19);
x_21 = l_Lake_EquipT_instMonad___redArg(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
lean_dec_ref(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_instAlternativeJobM___lam__0___boxed), 8, 0);
x_24 = lean_alloc_closure((void*)(l_Lake_instAlternativeJobM___lam__1), 10, 0);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
lean_inc(x_26);
lean_inc(x_28);
x_29 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_26);
lean_inc(x_26);
lean_inc(x_28);
x_30 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_26);
lean_inc_ref(x_29);
lean_inc(x_28);
x_31 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_31, 0, x_28);
lean_closure_set(x_31, 1, x_29);
lean_inc(x_28);
lean_inc_ref(x_27);
x_32 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_32, 0, x_27);
lean_closure_set(x_32, 1, x_28);
lean_closure_set(x_32, 2, x_26);
x_33 = l_Lake_EStateT_instFunctor___redArg(x_27);
x_34 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_34, 0, x_28);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_35);
x_36 = l_ReaderT_instMonad___redArg(x_1);
x_37 = l_ReaderT_instMonad___redArg(x_36);
x_38 = l_ReaderT_instMonad___redArg(x_37);
x_39 = l_ReaderT_instMonad___redArg(x_38);
x_40 = l_Lake_EquipT_instMonad___redArg(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
lean_dec_ref(x_40);
x_42 = lean_alloc_closure((void*)(l_Lake_instAlternativeJobM___lam__0___boxed), 8, 0);
x_43 = lean_alloc_closure((void*)(l_Lake_instAlternativeJobM___lam__1), 10, 0);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_45 = lean_ctor_get(x_1, 0);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 lean_ctor_release(x_45, 4);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
lean_inc(x_46);
lean_inc(x_48);
x_50 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_50, 0, x_48);
lean_closure_set(x_50, 1, x_46);
lean_inc(x_46);
lean_inc(x_48);
x_51 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_51, 0, x_48);
lean_closure_set(x_51, 1, x_46);
lean_inc_ref(x_50);
lean_inc(x_48);
x_52 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_52, 0, x_48);
lean_closure_set(x_52, 1, x_50);
lean_inc(x_48);
lean_inc_ref(x_47);
x_53 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_53, 0, x_47);
lean_closure_set(x_53, 1, x_48);
lean_closure_set(x_53, 2, x_46);
x_54 = l_Lake_EStateT_instFunctor___redArg(x_47);
x_55 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_55, 0, x_48);
if (lean_is_scalar(x_49)) {
 x_56 = lean_alloc_ctor(0, 5, 0);
} else {
 x_56 = x_49;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_50);
x_58 = l_ReaderT_instMonad___redArg(x_57);
x_59 = l_ReaderT_instMonad___redArg(x_58);
x_60 = l_ReaderT_instMonad___redArg(x_59);
x_61 = l_ReaderT_instMonad___redArg(x_60);
x_62 = l_Lake_EquipT_instMonad___redArg(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
lean_dec_ref(x_62);
x_64 = lean_alloc_closure((void*)(l_Lake_instAlternativeJobM___lam__0___boxed), 8, 0);
x_65 = lean_alloc_closure((void*)(l_Lake_instAlternativeJobM___lam__1), 10, 0);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
return x_66;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_instAlternativeJobM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_apply_2(x_2, x_11, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_8, 0, x_17);
lean_ctor_set(x_13, 1, x_8);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_12, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_8, 0, x_30);
lean_ctor_set(x_13, 1, x_8);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set(x_12, 0, x_33);
return x_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_37 = x_13;
} else {
 lean_dec_ref(x_13);
 x_37 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_36);
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_8);
x_43 = lean_apply_2(x_2, x_40, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
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
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
}
}
static lean_object* _init_l_Lake_instMonadLiftLogIOJobM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instMonadLiftLogIOJobM___lam__0___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_instMonadLiftLogIOJobM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_6 = lean_box(0);
x_7 = l_Lake_JobAction_merge(x_5, x_1);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l_Lake_JobAction_merge(x_11, x_1);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_11 = lean_box(0);
x_12 = l_Lake_JobAction_merge(x_10, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = l_Lake_JobAction_merge(x_16, x_1);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lake_updateAction___redArg(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_Lake_updateAction(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_getTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_2, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_9);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_setTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = l_Lake_BuildTrace_nil(x_1);
x_7 = lean_box(0);
lean_ctor_set(x_2, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Lake_BuildTrace_nil(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = l_Lake_BuildTrace_nil(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_7, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_15);
lean_dec(x_7);
x_17 = l_Lake_BuildTrace_nil(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_newTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_1, x_5);
lean_ctor_set(x_2, 1, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_1, x_12);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_1, x_10);
lean_ctor_set(x_7, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = lean_apply_1(x_1, x_17);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_modifyTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_5, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
lean_inc(x_11);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_12);
lean_ctor_set(x_2, 1, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_18);
lean_inc(x_19);
lean_dec(x_2);
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
x_22 = lean_ctor_get_uint64(x_18, sizeof(void*)*3);
x_23 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_23);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_24 = x_18;
} else {
 lean_dec_ref(x_18);
 x_24 = lean_box(0);
}
x_25 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 3, 8);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set_uint64(x_26, sizeof(void*)*3, x_22);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get_uint64(x_10, sizeof(void*)*3);
x_18 = lean_ctor_get(x_10, 2);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set_uint64(x_20, sizeof(void*)*3, x_17);
lean_ctor_set(x_7, 1, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
lean_inc(x_23);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_26);
x_27 = lean_ctor_get_uint64(x_23, sizeof(void*)*3);
x_28 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_28);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_29 = x_23;
} else {
 lean_dec_ref(x_23);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 3, 8);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_27);
x_32 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_8);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_setTraceCaption(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_takeTrace___redArg___closed__0;
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_takeTrace___redArg___closed__1;
lean_ctor_set(x_1, 1, x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_8);
lean_dec(x_1);
x_11 = l_Lake_takeTrace___redArg___closed__1;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lake_takeTrace___redArg___closed__1;
lean_ctor_set(x_6, 1, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_13);
lean_dec(x_6);
x_16 = l_Lake_takeTrace___redArg___closed__1;
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_takeTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_ctor_set(x_2, 1, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_8);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_ctor_set(x_7, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_13);
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_swapTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_box(0);
x_7 = l_Lake_BuildTrace_mix(x_5, x_1);
lean_ctor_set(x_2, 1, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_10);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l_Lake_BuildTrace_mix(x_12, x_1);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_box(0);
x_12 = l_Lake_BuildTrace_mix(x_10, x_1);
lean_ctor_set(x_7, 1, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_15);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = l_Lake_BuildTrace_mix(x_17, x_1);
x_20 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_addTrace(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lake_BuildTrace_nil(x_1);
lean_ctor_set(x_8, 1, x_12);
x_13 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 1);
x_22 = l_Lake_BuildTrace_mix(x_11, x_21);
lean_ctor_set(x_15, 1, x_22);
return x_13;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_23);
lean_dec(x_15);
x_26 = l_Lake_BuildTrace_mix(x_11, x_25);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_24);
lean_ctor_set(x_14, 1, x_27);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_31 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_31);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_32 = x_15;
} else {
 lean_dec_ref(x_15);
 x_32 = lean_box(0);
}
x_33 = l_Lake_BuildTrace_mix(x_11, x_31);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_13, 0, x_35);
return x_13;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_38 = x_14;
} else {
 lean_dec_ref(x_14);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
x_41 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_42 = x_15;
} else {
 lean_dec_ref(x_15);
 x_42 = lean_box(0);
}
x_43 = l_Lake_BuildTrace_mix(x_11, x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 1);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_40);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
return x_46;
}
}
else
{
lean_dec(x_14);
lean_dec_ref(x_11);
return x_13;
}
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_inc(x_47);
lean_dec(x_8);
x_50 = l_Lake_BuildTrace_nil(x_1);
x_51 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_48);
x_52 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_51, x_9);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_58 = x_53;
} else {
 lean_dec_ref(x_53);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get_uint8(x_54, sizeof(void*)*2);
x_61 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
x_63 = l_Lake_BuildTrace_mix(x_49, x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 1);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_60);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_64);
if (lean_is_scalar(x_56)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_56;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_55);
return x_66;
}
else
{
lean_dec(x_53);
lean_dec_ref(x_49);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lake_BuildTrace_nil(x_2);
lean_ctor_set(x_9, 1, x_13);
x_14 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 1);
x_23 = l_Lake_BuildTrace_mix(x_12, x_22);
lean_ctor_set(x_16, 1, x_23);
return x_14;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_24);
lean_dec(x_16);
x_27 = l_Lake_BuildTrace_mix(x_12, x_26);
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_25);
lean_ctor_set(x_15, 1, x_28);
return x_14;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_32 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_33 = x_16;
} else {
 lean_dec_ref(x_16);
 x_33 = lean_box(0);
}
x_34 = l_Lake_BuildTrace_mix(x_12, x_32);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 1);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_14, 0, x_36);
return x_14;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_39 = x_15;
} else {
 lean_dec_ref(x_15);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
x_42 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_42);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_43 = x_16;
} else {
 lean_dec_ref(x_16);
 x_43 = lean_box(0);
}
x_44 = l_Lake_BuildTrace_mix(x_12, x_42);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 1);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_39)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_39;
}
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
return x_47;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_12);
return x_14;
}
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_inc(x_48);
lean_dec(x_9);
x_51 = l_Lake_BuildTrace_nil(x_2);
x_52 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_49);
x_53 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_52, x_10);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_60);
x_61 = lean_ctor_get_uint8(x_55, sizeof(void*)*2);
x_62 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
 x_63 = lean_box(0);
}
x_64 = l_Lake_BuildTrace_mix(x_50, x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 1);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_61);
if (lean_is_scalar(x_59)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_59;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_57)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_57;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_56);
return x_67;
}
else
{
lean_dec(x_54);
lean_dec_ref(x_50);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_9);
x_10 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
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
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
x_11 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lake_instMonadLiftSpawnMJobM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JobM_runSpawnM), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadLiftSpawnMJobM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instMonadLiftSpawnMJobM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = 0;
x_10 = l_Lake_takeTrace___redArg___closed__1;
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_9);
x_12 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_11, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_19);
lean_dec(x_14);
lean_ctor_set(x_13, 1, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_25 = x_13;
} else {
 lean_dec_ref(x_13);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_26);
lean_dec(x_14);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_12, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_13, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_34);
lean_dec(x_29);
lean_ctor_set(x_13, 1, x_34);
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_12, 0, x_37);
return x_12;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_12, 1);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_ctor_get(x_13, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_40 = x_13;
} else {
 lean_dec_ref(x_13);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_41);
lean_dec(x_29);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = 0;
x_11 = l_Lake_takeTrace___redArg___closed__1;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
x_13 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_12, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_20);
lean_dec(x_15);
lean_ctor_set(x_14, 1, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_22);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_26 = x_14;
} else {
 lean_dec_ref(x_14);
 x_26 = lean_box(0);
}
x_27 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_27);
lean_dec(x_15);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_13, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_14, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_35);
lean_dec(x_30);
lean_ctor_set(x_14, 1, x_35);
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_37);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_41 = x_14;
} else {
 lean_dec_ref(x_14);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_42);
lean_dec(x_30);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
}
static lean_object* _init_l_Lake_instMonadLiftJobMFetchM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_FetchM_runJobM), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadLiftJobMFetchM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instMonadLiftJobMFetchM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_7, 0, x_16);
lean_ctor_set(x_12, 1, x_7);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_23 = x_12;
} else {
 lean_dec_ref(x_12);
 x_23 = lean_box(0);
}
lean_ctor_set(x_7, 0, x_22);
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_11, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 1);
lean_ctor_set(x_7, 0, x_29);
lean_ctor_set(x_12, 1, x_7);
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_31);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_11, 0, x_32);
return x_11;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_dec(x_11);
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_36 = x_12;
} else {
 lean_dec_ref(x_12);
 x_36 = lean_box(0);
}
lean_ctor_set(x_7, 0, x_35);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_7);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get_uint8(x_7, sizeof(void*)*2);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_inc(x_39);
lean_dec(x_7);
x_42 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_39, x_8);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_40);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_53 = x_42;
} else {
 lean_dec_ref(x_42);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_56 = x_43;
} else {
 lean_dec_ref(x_43);
 x_56 = lean_box(0);
}
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_40);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
if (lean_is_scalar(x_53)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_53;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_8, 0, x_17);
lean_ctor_set(x_13, 1, x_8);
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_8);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_12, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_13, 1);
lean_ctor_set(x_8, 0, x_30);
lean_ctor_set(x_13, 1, x_8);
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_32);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_8);
lean_ctor_set(x_12, 0, x_33);
return x_12;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_12, 1);
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_37 = x_13;
} else {
 lean_dec_ref(x_13);
 x_37 = lean_box(0);
}
lean_ctor_set(x_8, 0, x_36);
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_8);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get_uint8(x_8, sizeof(void*)*2);
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_8);
x_43 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_40, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
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
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_46)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_46;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_44, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_44, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_57 = x_44;
} else {
 lean_dec_ref(x_44);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_42);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_41);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_54;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
}
}
static lean_object* _init_l_Lake_instMonadLiftFetchMJobM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_JobM_runFetchM), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instMonadLiftFetchMJobM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instMonadLiftFetchMJobM___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_3);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_8);
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec_ref(x_5);
x_11 = lean_apply_1(x_3, x_7);
x_12 = lean_box(x_9);
x_13 = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_10);
x_14 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec_ref(x_4);
x_10 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*3);
lean_dec_ref(x_7);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = lean_apply_1(x_6, x_10);
x_15 = lean_box(x_12);
x_16 = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_16, 0, x_5);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_13);
x_17 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_14, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_Job_bindTask___redArg___lam__0(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout/stderr:\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_IO_FS_withIsolatedStreams___redArg(x_1, x_2, x_3, x_4, x_5);
x_15 = lean_apply_7(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; uint8_t x_30; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_21 = x_16;
} else {
 lean_dec_ref(x_16);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_29 = lean_string_utf8_byte_size(x_22);
x_30 = lean_nat_dec_eq(x_29, x_12);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_34 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_35 = l_Substring_takeWhileAux(x_22, x_29, x_34, x_12);
x_36 = l_Substring_takeRightWhileAux(x_22, x_35, x_34, x_29);
x_37 = lean_string_utf8_extract(x_22, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_22);
x_38 = lean_string_append(x_33, x_37);
lean_dec_ref(x_37);
x_39 = 1;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_push(x_32, x_40);
lean_ctor_set(x_20, 0, x_41);
x_24 = x_20;
x_25 = x_18;
goto block_28;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_42);
lean_dec(x_20);
x_45 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_46 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_47 = l_Substring_takeWhileAux(x_22, x_29, x_46, x_12);
x_48 = l_Substring_takeRightWhileAux(x_22, x_47, x_46, x_29);
x_49 = lean_string_utf8_extract(x_22, x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_22);
x_50 = lean_string_append(x_45, x_49);
lean_dec_ref(x_49);
x_51 = 1;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_push(x_42, x_52);
x_54 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_43);
x_24 = x_54;
x_25 = x_18;
goto block_28;
}
}
else
{
lean_dec(x_29);
lean_dec(x_22);
lean_dec(x_12);
x_24 = x_20;
x_25 = x_18;
goto block_28;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
if (lean_is_scalar(x_21)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_21;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
if (lean_is_scalar(x_19)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_19;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_55; 
lean_dec(x_12);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_15, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
return x_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_16, 0);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_16);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_15, 0, x_60);
return x_15;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_15, 1);
lean_inc(x_61);
lean_dec(x_15);
x_62 = lean_ctor_get(x_16, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_64 = x_16;
} else {
 lean_dec_ref(x_16);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Job_async___redArg___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadStateOfJobStateJobM___closed__3;
x_2 = l_Lake_Job_async___redArg___closed__1;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadStateOfJobStateJobM___closed__4;
x_2 = l_Lake_Job_async___redArg___closed__2;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadStateOfJobStateJobM___closed__3;
x_2 = l_Lake_Job_async___redArg___closed__3;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadStateOfJobStateJobM___closed__3;
x_2 = l_Lake_Job_async___redArg___closed__4;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadStateOfJobStateJobM___closed__2;
x_2 = l_Lake_Job_async___redArg___closed__5;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_instMonadLiftFetchMJobM___closed__0;
x_2 = l_Lake_Job_async___redArg___closed__6;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Job_async___redArg___closed__9() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_takeTrace___redArg___closed__1;
x_2 = 0;
x_3 = l_Lake_Job_async___redArg___closed__8;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 4);
lean_dec(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_dec(x_19);
x_20 = lean_ctor_get(x_13, 2);
lean_dec(x_20);
lean_inc(x_15);
lean_inc(x_17);
x_21 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_15);
lean_inc(x_15);
lean_inc(x_17);
x_22 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_22, 0, x_17);
lean_closure_set(x_22, 1, x_15);
lean_inc_ref(x_21);
lean_inc(x_17);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_21);
lean_inc(x_15);
lean_inc(x_17);
lean_inc_ref(x_16);
x_24 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_24, 0, x_16);
lean_closure_set(x_24, 1, x_17);
lean_closure_set(x_24, 2, x_15);
x_25 = l_Lake_EStateT_instFunctor___redArg(x_16);
lean_inc(x_17);
x_26 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_26, 0, x_17);
lean_ctor_set(x_13, 4, x_22);
lean_ctor_set(x_13, 3, x_23);
lean_ctor_set(x_13, 2, x_24);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_11, 1, x_21);
x_27 = l_ReaderT_instMonad___redArg(x_11);
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = l_ReaderT_instMonad___redArg(x_28);
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = l_Lake_EquipT_instMonad___redArg(x_30);
x_32 = l_Lake_Job_async___redArg___closed__7;
x_33 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_33, 0, x_17);
lean_closure_set(x_33, 1, x_15);
x_34 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lake_Job_async___redArg___closed__9;
x_41 = 1;
x_42 = lean_box(x_41);
x_43 = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__0___boxed), 13, 12);
lean_closure_set(x_43, 0, x_31);
lean_closure_set(x_43, 1, x_38);
lean_closure_set(x_43, 2, x_32);
lean_closure_set(x_43, 3, x_2);
lean_closure_set(x_43, 4, x_42);
lean_closure_set(x_43, 5, x_5);
lean_closure_set(x_43, 6, x_6);
lean_closure_set(x_43, 7, x_7);
lean_closure_set(x_43, 8, x_8);
lean_closure_set(x_43, 9, x_9);
lean_closure_set(x_43, 10, x_40);
lean_closure_set(x_43, 11, x_39);
x_44 = lean_io_as_task(x_43, x_3, x_10);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_1);
lean_ctor_set(x_48, 2, x_4);
lean_ctor_set_uint8(x_48, sizeof(void*)*3, x_47);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = 0;
x_52 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_1);
lean_ctor_set(x_52, 2, x_4);
lean_ctor_set_uint8(x_52, sizeof(void*)*3, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_54 = lean_ctor_get(x_11, 1);
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
lean_inc(x_54);
lean_inc(x_56);
x_57 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_57, 0, x_56);
lean_closure_set(x_57, 1, x_54);
lean_inc(x_54);
lean_inc(x_56);
x_58 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_58, 0, x_56);
lean_closure_set(x_58, 1, x_54);
lean_inc_ref(x_57);
lean_inc(x_56);
x_59 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_59, 0, x_56);
lean_closure_set(x_59, 1, x_57);
lean_inc(x_54);
lean_inc(x_56);
lean_inc_ref(x_55);
x_60 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_60, 0, x_55);
lean_closure_set(x_60, 1, x_56);
lean_closure_set(x_60, 2, x_54);
x_61 = l_Lake_EStateT_instFunctor___redArg(x_55);
lean_inc(x_56);
x_62 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_62, 0, x_56);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_60);
lean_ctor_set(x_63, 3, x_59);
lean_ctor_set(x_63, 4, x_58);
lean_ctor_set(x_11, 1, x_57);
lean_ctor_set(x_11, 0, x_63);
x_64 = l_ReaderT_instMonad___redArg(x_11);
x_65 = l_ReaderT_instMonad___redArg(x_64);
x_66 = l_ReaderT_instMonad___redArg(x_65);
x_67 = l_ReaderT_instMonad___redArg(x_66);
x_68 = l_Lake_EquipT_instMonad___redArg(x_67);
x_69 = l_Lake_Job_async___redArg___closed__7;
x_70 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_70, 0, x_56);
lean_closure_set(x_70, 1, x_54);
x_71 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_70);
x_72 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_72, 0, x_71);
x_73 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_73, 0, x_72);
x_74 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_74, 0, x_73);
x_75 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_75, 0, x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l_Lake_Job_async___redArg___closed__9;
x_78 = 1;
x_79 = lean_box(x_78);
x_80 = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__0___boxed), 13, 12);
lean_closure_set(x_80, 0, x_68);
lean_closure_set(x_80, 1, x_75);
lean_closure_set(x_80, 2, x_69);
lean_closure_set(x_80, 3, x_2);
lean_closure_set(x_80, 4, x_79);
lean_closure_set(x_80, 5, x_5);
lean_closure_set(x_80, 6, x_6);
lean_closure_set(x_80, 7, x_7);
lean_closure_set(x_80, 8, x_8);
lean_closure_set(x_80, 9, x_9);
lean_closure_set(x_80, 10, x_77);
lean_closure_set(x_80, 11, x_76);
x_81 = lean_io_as_task(x_80, x_3, x_10);
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
x_85 = 0;
x_86 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_1);
lean_ctor_set(x_86, 2, x_4);
lean_ctor_set_uint8(x_86, sizeof(void*)*3, x_85);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
x_88 = lean_ctor_get(x_11, 0);
x_89 = lean_ctor_get(x_11, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_11);
x_90 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
lean_inc(x_89);
lean_inc(x_91);
x_93 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_93, 0, x_91);
lean_closure_set(x_93, 1, x_89);
lean_inc(x_89);
lean_inc(x_91);
x_94 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_94, 0, x_91);
lean_closure_set(x_94, 1, x_89);
lean_inc_ref(x_93);
lean_inc(x_91);
x_95 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_95, 0, x_91);
lean_closure_set(x_95, 1, x_93);
lean_inc(x_89);
lean_inc(x_91);
lean_inc_ref(x_90);
x_96 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_96, 0, x_90);
lean_closure_set(x_96, 1, x_91);
lean_closure_set(x_96, 2, x_89);
x_97 = l_Lake_EStateT_instFunctor___redArg(x_90);
lean_inc(x_91);
x_98 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_98, 0, x_91);
if (lean_is_scalar(x_92)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_92;
}
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_95);
lean_ctor_set(x_99, 4, x_94);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_93);
x_101 = l_ReaderT_instMonad___redArg(x_100);
x_102 = l_ReaderT_instMonad___redArg(x_101);
x_103 = l_ReaderT_instMonad___redArg(x_102);
x_104 = l_ReaderT_instMonad___redArg(x_103);
x_105 = l_Lake_EquipT_instMonad___redArg(x_104);
x_106 = l_Lake_Job_async___redArg___closed__7;
x_107 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_107, 0, x_91);
lean_closure_set(x_107, 1, x_89);
x_108 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_108, 0, x_107);
x_109 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_109, 0, x_108);
x_110 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_111, 0, x_110);
x_112 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_112, 0, x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Lake_Job_async___redArg___closed__9;
x_115 = 1;
x_116 = lean_box(x_115);
x_117 = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__0___boxed), 13, 12);
lean_closure_set(x_117, 0, x_105);
lean_closure_set(x_117, 1, x_112);
lean_closure_set(x_117, 2, x_106);
lean_closure_set(x_117, 3, x_2);
lean_closure_set(x_117, 4, x_116);
lean_closure_set(x_117, 5, x_5);
lean_closure_set(x_117, 6, x_6);
lean_closure_set(x_117, 7, x_7);
lean_closure_set(x_117, 8, x_8);
lean_closure_set(x_117, 9, x_9);
lean_closure_set(x_117, 10, x_114);
lean_closure_set(x_117, 11, x_113);
x_118 = lean_io_as_task(x_117, x_3, x_10);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = 0;
x_123 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_1);
lean_ctor_set(x_123, 2, x_4);
lean_ctor_set_uint8(x_123, sizeof(void*)*3, x_122);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_120);
return x_124;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 2);
lean_dec(x_22);
lean_inc(x_17);
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_17);
lean_inc(x_17);
lean_inc(x_19);
x_24 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_17);
lean_inc_ref(x_23);
lean_inc(x_19);
x_25 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_25, 0, x_19);
lean_closure_set(x_25, 1, x_23);
lean_inc(x_17);
lean_inc(x_19);
lean_inc_ref(x_18);
x_26 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_26, 0, x_18);
lean_closure_set(x_26, 1, x_19);
lean_closure_set(x_26, 2, x_17);
x_27 = l_Lake_EStateT_instFunctor___redArg(x_18);
lean_inc(x_19);
x_28 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_28, 0, x_19);
lean_ctor_set(x_15, 4, x_24);
lean_ctor_set(x_15, 3, x_25);
lean_ctor_set(x_15, 2, x_26);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_27);
lean_ctor_set(x_13, 1, x_23);
x_29 = l_ReaderT_instMonad___redArg(x_13);
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = l_ReaderT_instMonad___redArg(x_31);
x_33 = l_Lake_EquipT_instMonad___redArg(x_32);
x_34 = l_Lake_Job_async___redArg___closed__7;
x_35 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_35, 0, x_19);
lean_closure_set(x_35, 1, x_17);
x_36 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lake_Job_async___redArg___closed__9;
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__0___boxed), 13, 12);
lean_closure_set(x_45, 0, x_33);
lean_closure_set(x_45, 1, x_40);
lean_closure_set(x_45, 2, x_34);
lean_closure_set(x_45, 3, x_3);
lean_closure_set(x_45, 4, x_44);
lean_closure_set(x_45, 5, x_6);
lean_closure_set(x_45, 6, x_7);
lean_closure_set(x_45, 7, x_8);
lean_closure_set(x_45, 8, x_9);
lean_closure_set(x_45, 9, x_10);
lean_closure_set(x_45, 10, x_42);
lean_closure_set(x_45, 11, x_41);
x_46 = lean_io_as_task(x_45, x_4, x_12);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = 0;
x_50 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_2);
lean_ctor_set(x_50, 2, x_5);
lean_ctor_set_uint8(x_50, sizeof(void*)*3, x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = 0;
x_54 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_5);
lean_ctor_set_uint8(x_54, sizeof(void*)*3, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_56 = lean_ctor_get(x_13, 1);
x_57 = lean_ctor_get(x_15, 0);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_15);
lean_inc(x_56);
lean_inc(x_58);
x_59 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_59, 0, x_58);
lean_closure_set(x_59, 1, x_56);
lean_inc(x_56);
lean_inc(x_58);
x_60 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_60, 0, x_58);
lean_closure_set(x_60, 1, x_56);
lean_inc_ref(x_59);
lean_inc(x_58);
x_61 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_61, 0, x_58);
lean_closure_set(x_61, 1, x_59);
lean_inc(x_56);
lean_inc(x_58);
lean_inc_ref(x_57);
x_62 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_62, 0, x_57);
lean_closure_set(x_62, 1, x_58);
lean_closure_set(x_62, 2, x_56);
x_63 = l_Lake_EStateT_instFunctor___redArg(x_57);
lean_inc(x_58);
x_64 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_64, 0, x_58);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_60);
lean_ctor_set(x_13, 1, x_59);
lean_ctor_set(x_13, 0, x_65);
x_66 = l_ReaderT_instMonad___redArg(x_13);
x_67 = l_ReaderT_instMonad___redArg(x_66);
x_68 = l_ReaderT_instMonad___redArg(x_67);
x_69 = l_ReaderT_instMonad___redArg(x_68);
x_70 = l_Lake_EquipT_instMonad___redArg(x_69);
x_71 = l_Lake_Job_async___redArg___closed__7;
x_72 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_72, 0, x_58);
lean_closure_set(x_72, 1, x_56);
x_73 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_73, 0, x_72);
x_74 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_74, 0, x_73);
x_75 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_75, 0, x_74);
x_76 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_76, 0, x_75);
x_77 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_77, 0, x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lake_Job_async___redArg___closed__9;
x_80 = 1;
x_81 = lean_box(x_80);
x_82 = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__0___boxed), 13, 12);
lean_closure_set(x_82, 0, x_70);
lean_closure_set(x_82, 1, x_77);
lean_closure_set(x_82, 2, x_71);
lean_closure_set(x_82, 3, x_3);
lean_closure_set(x_82, 4, x_81);
lean_closure_set(x_82, 5, x_6);
lean_closure_set(x_82, 6, x_7);
lean_closure_set(x_82, 7, x_8);
lean_closure_set(x_82, 8, x_9);
lean_closure_set(x_82, 9, x_10);
lean_closure_set(x_82, 10, x_79);
lean_closure_set(x_82, 11, x_78);
x_83 = lean_io_as_task(x_82, x_4, x_12);
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
x_87 = 0;
x_88 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_2);
lean_ctor_set(x_88, 2, x_5);
lean_ctor_set_uint8(x_88, sizeof(void*)*3, x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_90 = lean_ctor_get(x_13, 0);
x_91 = lean_ctor_get(x_13, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_13);
x_92 = lean_ctor_get(x_90, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 lean_ctor_release(x_90, 2);
 lean_ctor_release(x_90, 3);
 lean_ctor_release(x_90, 4);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
lean_inc(x_91);
lean_inc(x_93);
x_95 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_95, 0, x_93);
lean_closure_set(x_95, 1, x_91);
lean_inc(x_91);
lean_inc(x_93);
x_96 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_96, 0, x_93);
lean_closure_set(x_96, 1, x_91);
lean_inc_ref(x_95);
lean_inc(x_93);
x_97 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_97, 0, x_93);
lean_closure_set(x_97, 1, x_95);
lean_inc(x_91);
lean_inc(x_93);
lean_inc_ref(x_92);
x_98 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_98, 0, x_92);
lean_closure_set(x_98, 1, x_93);
lean_closure_set(x_98, 2, x_91);
x_99 = l_Lake_EStateT_instFunctor___redArg(x_92);
lean_inc(x_93);
x_100 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_100, 0, x_93);
if (lean_is_scalar(x_94)) {
 x_101 = lean_alloc_ctor(0, 5, 0);
} else {
 x_101 = x_94;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_98);
lean_ctor_set(x_101, 3, x_97);
lean_ctor_set(x_101, 4, x_96);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
x_103 = l_ReaderT_instMonad___redArg(x_102);
x_104 = l_ReaderT_instMonad___redArg(x_103);
x_105 = l_ReaderT_instMonad___redArg(x_104);
x_106 = l_ReaderT_instMonad___redArg(x_105);
x_107 = l_Lake_EquipT_instMonad___redArg(x_106);
x_108 = l_Lake_Job_async___redArg___closed__7;
x_109 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_109, 0, x_93);
lean_closure_set(x_109, 1, x_91);
x_110 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_110, 0, x_109);
x_111 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_111, 0, x_110);
x_112 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_112, 0, x_111);
x_113 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_113, 0, x_112);
x_114 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_114, 0, x_113);
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Lake_Job_async___redArg___closed__9;
x_117 = 1;
x_118 = lean_box(x_117);
x_119 = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__0___boxed), 13, 12);
lean_closure_set(x_119, 0, x_107);
lean_closure_set(x_119, 1, x_114);
lean_closure_set(x_119, 2, x_108);
lean_closure_set(x_119, 3, x_3);
lean_closure_set(x_119, 4, x_118);
lean_closure_set(x_119, 5, x_6);
lean_closure_set(x_119, 6, x_7);
lean_closure_set(x_119, 7, x_8);
lean_closure_set(x_119, 8, x_9);
lean_closure_set(x_119, 9, x_10);
lean_closure_set(x_119, 10, x_116);
lean_closure_set(x_119, 11, x_115);
x_120 = lean_io_as_task(x_119, x_4, x_12);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = 0;
x_125 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_2);
lean_ctor_set(x_125, 2, x_5);
lean_ctor_set_uint8(x_125, sizeof(void*)*3, x_124);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
x_15 = l_Lake_Job_async___redArg___lam__0(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_async(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_io_wait(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_io_wait(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_io_wait(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_io_wait(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_box(0);
x_6 = lean_array_push(x_3, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_6, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 2);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_8);
lean_inc(x_8);
lean_inc(x_10);
x_15 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_8);
lean_inc_ref(x_14);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_16, 0, x_10);
lean_closure_set(x_16, 1, x_14);
lean_inc(x_10);
lean_inc_ref(x_9);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_17, 0, x_9);
lean_closure_set(x_17, 1, x_10);
lean_closure_set(x_17, 2, x_8);
x_18 = l_Lake_EStateT_instFunctor___redArg(x_9);
x_19 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_19, 0, x_10);
lean_ctor_set(x_6, 4, x_15);
lean_ctor_set(x_6, 3, x_16);
lean_ctor_set(x_6, 2, x_17);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_6, 0, x_18);
lean_ctor_set(x_4, 1, x_14);
x_20 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_1);
x_21 = lean_io_wait(x_20, x_3);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
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
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_27 = x_22;
} else {
 lean_dec_ref(x_22);
 x_27 = lean_box(0);
}
x_33 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_33);
lean_dec(x_26);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_array_get_size(x_33);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec_ref(x_33);
lean_dec_ref(x_4);
x_28 = x_2;
x_29 = x_23;
goto block_32;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_35, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec_ref(x_33);
lean_dec_ref(x_4);
x_28 = x_2;
x_29 = x_23;
goto block_32;
}
else
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_39 = lean_box(0);
x_40 = 0;
x_41 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_42 = l_Array_foldlMUnsafe_fold___redArg(x_4, x_38, x_33, x_40, x_41, x_39);
x_43 = lean_apply_2(x_42, x_2, x_23);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_28 = x_46;
x_29 = x_45;
goto block_32;
}
else
{
uint8_t x_47; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
}
block_32:
{
lean_object* x_30; lean_object* x_31; 
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_28);
if (lean_is_scalar(x_24)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_24;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_60 = x_21;
} else {
 lean_dec_ref(x_21);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_22, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_63 = x_22;
} else {
 lean_dec_ref(x_22);
 x_63 = lean_box(0);
}
x_69 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_69);
lean_dec(x_62);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_array_get_size(x_69);
x_72 = lean_nat_dec_lt(x_70, x_71);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec_ref(x_69);
lean_dec_ref(x_4);
x_64 = x_2;
x_65 = x_59;
goto block_68;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_71, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec_ref(x_69);
lean_dec_ref(x_4);
x_64 = x_2;
x_65 = x_59;
goto block_68;
}
else
{
lean_object* x_74; lean_object* x_75; size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_75 = lean_box(0);
x_76 = 0;
x_77 = lean_usize_of_nat(x_71);
lean_dec(x_71);
x_78 = l_Array_foldlMUnsafe_fold___redArg(x_4, x_74, x_69, x_76, x_77, x_75);
x_79 = lean_apply_2(x_78, x_2, x_59);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_64 = x_82;
x_65 = x_81;
goto block_68;
}
else
{
uint8_t x_83; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_79, 0);
lean_dec(x_84);
x_85 = !lean_is_exclusive(x_80);
if (x_85 == 0)
{
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_80);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_79, 0, x_88);
return x_79;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_dec(x_79);
x_90 = lean_ctor_get(x_80, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_92 = x_80;
} else {
 lean_dec_ref(x_80);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
}
}
}
block_68:
{
lean_object* x_66; lean_object* x_67; 
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_64);
if (lean_is_scalar(x_60)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_60;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_4, 1);
x_96 = lean_ctor_get(x_6, 0);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_6);
lean_inc(x_95);
lean_inc(x_97);
x_98 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_98, 0, x_97);
lean_closure_set(x_98, 1, x_95);
lean_inc(x_95);
lean_inc(x_97);
x_99 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_99, 0, x_97);
lean_closure_set(x_99, 1, x_95);
lean_inc_ref(x_98);
lean_inc(x_97);
x_100 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_100, 0, x_97);
lean_closure_set(x_100, 1, x_98);
lean_inc(x_97);
lean_inc_ref(x_96);
x_101 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_101, 0, x_96);
lean_closure_set(x_101, 1, x_97);
lean_closure_set(x_101, 2, x_95);
x_102 = l_Lake_EStateT_instFunctor___redArg(x_96);
x_103 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_103, 0, x_97);
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_4, 1, x_98);
lean_ctor_set(x_4, 0, x_104);
x_105 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_105);
lean_dec_ref(x_1);
x_106 = lean_io_wait(x_105, x_3);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_112 = x_107;
} else {
 lean_dec_ref(x_107);
 x_112 = lean_box(0);
}
x_118 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_118);
lean_dec(x_111);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_array_get_size(x_118);
x_121 = lean_nat_dec_lt(x_119, x_120);
if (x_121 == 0)
{
lean_dec(x_120);
lean_dec_ref(x_118);
lean_dec_ref(x_4);
x_113 = x_2;
x_114 = x_108;
goto block_117;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_le(x_120, x_120);
if (x_122 == 0)
{
lean_dec(x_120);
lean_dec_ref(x_118);
lean_dec_ref(x_4);
x_113 = x_2;
x_114 = x_108;
goto block_117;
}
else
{
lean_object* x_123; lean_object* x_124; size_t x_125; size_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_124 = lean_box(0);
x_125 = 0;
x_126 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_127 = l_Array_foldlMUnsafe_fold___redArg(x_4, x_123, x_118, x_125, x_126, x_124);
x_128 = lean_apply_2(x_127, x_2, x_108);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_113 = x_131;
x_114 = x_130;
goto block_117;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_133 = x_128;
} else {
 lean_dec_ref(x_128);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_136 = x_129;
} else {
 lean_dec_ref(x_129);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
if (lean_is_scalar(x_133)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_133;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_132);
return x_138;
}
}
}
block_117:
{
lean_object* x_115; lean_object* x_116; 
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_113);
if (lean_is_scalar(x_109)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_109;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_139 = lean_ctor_get(x_106, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_140 = x_106;
} else {
 lean_dec_ref(x_106);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_107, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_107, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_143 = x_107;
} else {
 lean_dec_ref(x_107);
 x_143 = lean_box(0);
}
x_149 = lean_ctor_get(x_142, 0);
lean_inc_ref(x_149);
lean_dec(x_142);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_array_get_size(x_149);
x_152 = lean_nat_dec_lt(x_150, x_151);
if (x_152 == 0)
{
lean_dec(x_151);
lean_dec_ref(x_149);
lean_dec_ref(x_4);
x_144 = x_2;
x_145 = x_139;
goto block_148;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_151, x_151);
if (x_153 == 0)
{
lean_dec(x_151);
lean_dec_ref(x_149);
lean_dec_ref(x_4);
x_144 = x_2;
x_145 = x_139;
goto block_148;
}
else
{
lean_object* x_154; lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_155 = lean_box(0);
x_156 = 0;
x_157 = lean_usize_of_nat(x_151);
lean_dec(x_151);
x_158 = l_Array_foldlMUnsafe_fold___redArg(x_4, x_154, x_149, x_156, x_157, x_155);
x_159 = lean_apply_2(x_158, x_2, x_139);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_144 = x_162;
x_145 = x_161;
goto block_148;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_140);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_164 = x_159;
} else {
 lean_dec_ref(x_159);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_160, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_167 = x_160;
} else {
 lean_dec_ref(x_160);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_164;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_163);
return x_169;
}
}
}
block_148:
{
lean_object* x_146; lean_object* x_147; 
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_141);
lean_ctor_set(x_146, 1, x_144);
if (lean_is_scalar(x_140)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_140;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_170 = lean_ctor_get(x_4, 0);
x_171 = lean_ctor_get(x_4, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_4);
x_172 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 x_174 = x_170;
} else {
 lean_dec_ref(x_170);
 x_174 = lean_box(0);
}
lean_inc(x_171);
lean_inc(x_173);
x_175 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_175, 0, x_173);
lean_closure_set(x_175, 1, x_171);
lean_inc(x_171);
lean_inc(x_173);
x_176 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_176, 0, x_173);
lean_closure_set(x_176, 1, x_171);
lean_inc_ref(x_175);
lean_inc(x_173);
x_177 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_177, 0, x_173);
lean_closure_set(x_177, 1, x_175);
lean_inc(x_173);
lean_inc_ref(x_172);
x_178 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_178, 0, x_172);
lean_closure_set(x_178, 1, x_173);
lean_closure_set(x_178, 2, x_171);
x_179 = l_Lake_EStateT_instFunctor___redArg(x_172);
x_180 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_180, 0, x_173);
if (lean_is_scalar(x_174)) {
 x_181 = lean_alloc_ctor(0, 5, 0);
} else {
 x_181 = x_174;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_177);
lean_ctor_set(x_181, 4, x_176);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_175);
x_183 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_183);
lean_dec_ref(x_1);
x_184 = lean_io_wait(x_183, x_3);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_190 = x_185;
} else {
 lean_dec_ref(x_185);
 x_190 = lean_box(0);
}
x_196 = lean_ctor_get(x_189, 0);
lean_inc_ref(x_196);
lean_dec(x_189);
x_197 = lean_unsigned_to_nat(0u);
x_198 = lean_array_get_size(x_196);
x_199 = lean_nat_dec_lt(x_197, x_198);
if (x_199 == 0)
{
lean_dec(x_198);
lean_dec_ref(x_196);
lean_dec_ref(x_182);
x_191 = x_2;
x_192 = x_186;
goto block_195;
}
else
{
uint8_t x_200; 
x_200 = lean_nat_dec_le(x_198, x_198);
if (x_200 == 0)
{
lean_dec(x_198);
lean_dec_ref(x_196);
lean_dec_ref(x_182);
x_191 = x_2;
x_192 = x_186;
goto block_195;
}
else
{
lean_object* x_201; lean_object* x_202; size_t x_203; size_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_202 = lean_box(0);
x_203 = 0;
x_204 = lean_usize_of_nat(x_198);
lean_dec(x_198);
x_205 = l_Array_foldlMUnsafe_fold___redArg(x_182, x_201, x_196, x_203, x_204, x_202);
x_206 = lean_apply_2(x_205, x_2, x_186);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_191 = x_209;
x_192 = x_208;
goto block_195;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_190);
lean_dec(x_188);
lean_dec(x_187);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_207, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_207, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_214 = x_207;
} else {
 lean_dec_ref(x_207);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_210);
return x_216;
}
}
}
block_195:
{
lean_object* x_193; lean_object* x_194; 
if (lean_is_scalar(x_190)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_190;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_191);
if (lean_is_scalar(x_187)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_187;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_217 = lean_ctor_get(x_184, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_218 = x_184;
} else {
 lean_dec_ref(x_184);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_185, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_185, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_221 = x_185;
} else {
 lean_dec_ref(x_185);
 x_221 = lean_box(0);
}
x_227 = lean_ctor_get(x_220, 0);
lean_inc_ref(x_227);
lean_dec(x_220);
x_228 = lean_unsigned_to_nat(0u);
x_229 = lean_array_get_size(x_227);
x_230 = lean_nat_dec_lt(x_228, x_229);
if (x_230 == 0)
{
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_182);
x_222 = x_2;
x_223 = x_217;
goto block_226;
}
else
{
uint8_t x_231; 
x_231 = lean_nat_dec_le(x_229, x_229);
if (x_231 == 0)
{
lean_dec(x_229);
lean_dec_ref(x_227);
lean_dec_ref(x_182);
x_222 = x_2;
x_223 = x_217;
goto block_226;
}
else
{
lean_object* x_232; lean_object* x_233; size_t x_234; size_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_232 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_233 = lean_box(0);
x_234 = 0;
x_235 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_236 = l_Array_foldlMUnsafe_fold___redArg(x_182, x_232, x_227, x_234, x_235, x_233);
x_237 = lean_apply_2(x_236, x_2, x_217);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_222 = x_240;
x_223 = x_239;
goto block_226;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_218);
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_242 = x_237;
} else {
 lean_dec_ref(x_237);
 x_242 = lean_box(0);
}
x_243 = lean_ctor_get(x_238, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_238, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_245 = x_238;
} else {
 lean_dec_ref(x_238);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
if (lean_is_scalar(x_242)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_242;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_241);
return x_247;
}
}
}
block_226:
{
lean_object* x_224; lean_object* x_225; 
if (lean_is_scalar(x_221)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_221;
}
lean_ctor_set(x_224, 0, x_219);
lean_ctor_set(x_224, 1, x_222);
if (lean_is_scalar(x_218)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_218;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 2);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_9);
lean_inc(x_9);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_16, 0, x_11);
lean_closure_set(x_16, 1, x_9);
lean_inc_ref(x_15);
lean_inc(x_11);
x_17 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_17, 0, x_11);
lean_closure_set(x_17, 1, x_15);
lean_inc(x_11);
lean_inc_ref(x_10);
x_18 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_18, 0, x_10);
lean_closure_set(x_18, 1, x_11);
lean_closure_set(x_18, 2, x_9);
x_19 = l_Lake_EStateT_instFunctor___redArg(x_10);
x_20 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_20, 0, x_11);
lean_ctor_set(x_7, 4, x_16);
lean_ctor_set(x_7, 3, x_17);
lean_ctor_set(x_7, 2, x_18);
lean_ctor_set(x_7, 1, x_20);
lean_ctor_set(x_7, 0, x_19);
lean_ctor_set(x_5, 1, x_15);
x_21 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_2);
x_22 = lean_io_wait(x_21, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
x_34 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_34);
lean_dec(x_27);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_5);
x_29 = x_3;
x_30 = x_24;
goto block_33;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_36, x_36);
if (x_38 == 0)
{
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_5);
x_29 = x_3;
x_30 = x_24;
goto block_33;
}
else
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_40 = lean_box(0);
x_41 = 0;
x_42 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_43 = l_Array_foldlMUnsafe_fold___redArg(x_5, x_39, x_34, x_41, x_42, x_40);
x_44 = lean_apply_2(x_43, x_3, x_24);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_29 = x_47;
x_30 = x_46;
goto block_33;
}
else
{
uint8_t x_48; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_44, 0, x_53);
return x_44;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_57 = x_45;
} else {
 lean_dec_ref(x_45);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
}
}
block_33:
{
lean_object* x_31; lean_object* x_32; 
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_29);
if (lean_is_scalar(x_25)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_25;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_61 = x_22;
} else {
 lean_dec_ref(x_22);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_23, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_64 = x_23;
} else {
 lean_dec_ref(x_23);
 x_64 = lean_box(0);
}
x_70 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_70);
lean_dec(x_63);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_array_get_size(x_70);
x_73 = lean_nat_dec_lt(x_71, x_72);
if (x_73 == 0)
{
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_5);
x_65 = x_3;
x_66 = x_60;
goto block_69;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_72, x_72);
if (x_74 == 0)
{
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec_ref(x_5);
x_65 = x_3;
x_66 = x_60;
goto block_69;
}
else
{
lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_76 = lean_box(0);
x_77 = 0;
x_78 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_79 = l_Array_foldlMUnsafe_fold___redArg(x_5, x_75, x_70, x_77, x_78, x_76);
x_80 = lean_apply_2(x_79, x_3, x_60);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_65 = x_83;
x_66 = x_82;
goto block_69;
}
else
{
uint8_t x_84; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_80, 0);
lean_dec(x_85);
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_80;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_80, 0, x_89);
return x_80;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_80, 1);
lean_inc(x_90);
lean_dec(x_80);
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_90);
return x_95;
}
}
}
}
block_69:
{
lean_object* x_67; lean_object* x_68; 
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_65);
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_61;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_96 = lean_ctor_get(x_5, 1);
x_97 = lean_ctor_get(x_7, 0);
x_98 = lean_ctor_get(x_7, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_7);
lean_inc(x_96);
lean_inc(x_98);
x_99 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_99, 0, x_98);
lean_closure_set(x_99, 1, x_96);
lean_inc(x_96);
lean_inc(x_98);
x_100 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_100, 0, x_98);
lean_closure_set(x_100, 1, x_96);
lean_inc_ref(x_99);
lean_inc(x_98);
x_101 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_101, 0, x_98);
lean_closure_set(x_101, 1, x_99);
lean_inc(x_98);
lean_inc_ref(x_97);
x_102 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_102, 0, x_97);
lean_closure_set(x_102, 1, x_98);
lean_closure_set(x_102, 2, x_96);
x_103 = l_Lake_EStateT_instFunctor___redArg(x_97);
x_104 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_104, 0, x_98);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_101);
lean_ctor_set(x_105, 4, x_100);
lean_ctor_set(x_5, 1, x_99);
lean_ctor_set(x_5, 0, x_105);
x_106 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_106);
lean_dec_ref(x_2);
x_107 = lean_io_wait(x_106, x_4);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_113 = x_108;
} else {
 lean_dec_ref(x_108);
 x_113 = lean_box(0);
}
x_119 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_119);
lean_dec(x_112);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_array_get_size(x_119);
x_122 = lean_nat_dec_lt(x_120, x_121);
if (x_122 == 0)
{
lean_dec(x_121);
lean_dec_ref(x_119);
lean_dec_ref(x_5);
x_114 = x_3;
x_115 = x_109;
goto block_118;
}
else
{
uint8_t x_123; 
x_123 = lean_nat_dec_le(x_121, x_121);
if (x_123 == 0)
{
lean_dec(x_121);
lean_dec_ref(x_119);
lean_dec_ref(x_5);
x_114 = x_3;
x_115 = x_109;
goto block_118;
}
else
{
lean_object* x_124; lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_125 = lean_box(0);
x_126 = 0;
x_127 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_128 = l_Array_foldlMUnsafe_fold___redArg(x_5, x_124, x_119, x_126, x_127, x_125);
x_129 = lean_apply_2(x_128, x_3, x_109);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_114 = x_132;
x_115 = x_131;
goto block_118;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_110);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_137 = x_130;
} else {
 lean_dec_ref(x_130);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
if (lean_is_scalar(x_134)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_134;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_133);
return x_139;
}
}
}
block_118:
{
lean_object* x_116; lean_object* x_117; 
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_114);
if (lean_is_scalar(x_110)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_110;
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_140 = lean_ctor_get(x_107, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_141 = x_107;
} else {
 lean_dec_ref(x_107);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_108, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_108, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_144 = x_108;
} else {
 lean_dec_ref(x_108);
 x_144 = lean_box(0);
}
x_150 = lean_ctor_get(x_143, 0);
lean_inc_ref(x_150);
lean_dec(x_143);
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_array_get_size(x_150);
x_153 = lean_nat_dec_lt(x_151, x_152);
if (x_153 == 0)
{
lean_dec(x_152);
lean_dec_ref(x_150);
lean_dec_ref(x_5);
x_145 = x_3;
x_146 = x_140;
goto block_149;
}
else
{
uint8_t x_154; 
x_154 = lean_nat_dec_le(x_152, x_152);
if (x_154 == 0)
{
lean_dec(x_152);
lean_dec_ref(x_150);
lean_dec_ref(x_5);
x_145 = x_3;
x_146 = x_140;
goto block_149;
}
else
{
lean_object* x_155; lean_object* x_156; size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_156 = lean_box(0);
x_157 = 0;
x_158 = lean_usize_of_nat(x_152);
lean_dec(x_152);
x_159 = l_Array_foldlMUnsafe_fold___redArg(x_5, x_155, x_150, x_157, x_158, x_156);
x_160 = lean_apply_2(x_159, x_3, x_140);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_145 = x_163;
x_146 = x_162;
goto block_149;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_165 = x_160;
} else {
 lean_dec_ref(x_160);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_161, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_168 = x_161;
} else {
 lean_dec_ref(x_161);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
if (lean_is_scalar(x_165)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_165;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_164);
return x_170;
}
}
}
block_149:
{
lean_object* x_147; lean_object* x_148; 
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_145);
if (lean_is_scalar(x_141)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_141;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_171 = lean_ctor_get(x_5, 0);
x_172 = lean_ctor_get(x_5, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_5);
x_173 = lean_ctor_get(x_171, 0);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 x_175 = x_171;
} else {
 lean_dec_ref(x_171);
 x_175 = lean_box(0);
}
lean_inc(x_172);
lean_inc(x_174);
x_176 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_176, 0, x_174);
lean_closure_set(x_176, 1, x_172);
lean_inc(x_172);
lean_inc(x_174);
x_177 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_177, 0, x_174);
lean_closure_set(x_177, 1, x_172);
lean_inc_ref(x_176);
lean_inc(x_174);
x_178 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_178, 0, x_174);
lean_closure_set(x_178, 1, x_176);
lean_inc(x_174);
lean_inc_ref(x_173);
x_179 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_179, 0, x_173);
lean_closure_set(x_179, 1, x_174);
lean_closure_set(x_179, 2, x_172);
x_180 = l_Lake_EStateT_instFunctor___redArg(x_173);
x_181 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_181, 0, x_174);
if (lean_is_scalar(x_175)) {
 x_182 = lean_alloc_ctor(0, 5, 0);
} else {
 x_182 = x_175;
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_179);
lean_ctor_set(x_182, 3, x_178);
lean_ctor_set(x_182, 4, x_177);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_176);
x_184 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_184);
lean_dec_ref(x_2);
x_185 = lean_io_wait(x_184, x_4);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_191 = x_186;
} else {
 lean_dec_ref(x_186);
 x_191 = lean_box(0);
}
x_197 = lean_ctor_get(x_190, 0);
lean_inc_ref(x_197);
lean_dec(x_190);
x_198 = lean_unsigned_to_nat(0u);
x_199 = lean_array_get_size(x_197);
x_200 = lean_nat_dec_lt(x_198, x_199);
if (x_200 == 0)
{
lean_dec(x_199);
lean_dec_ref(x_197);
lean_dec_ref(x_183);
x_192 = x_3;
x_193 = x_187;
goto block_196;
}
else
{
uint8_t x_201; 
x_201 = lean_nat_dec_le(x_199, x_199);
if (x_201 == 0)
{
lean_dec(x_199);
lean_dec_ref(x_197);
lean_dec_ref(x_183);
x_192 = x_3;
x_193 = x_187;
goto block_196;
}
else
{
lean_object* x_202; lean_object* x_203; size_t x_204; size_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_203 = lean_box(0);
x_204 = 0;
x_205 = lean_usize_of_nat(x_199);
lean_dec(x_199);
x_206 = l_Array_foldlMUnsafe_fold___redArg(x_183, x_202, x_197, x_204, x_205, x_203);
x_207 = lean_apply_2(x_206, x_3, x_187);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_192 = x_210;
x_193 = x_209;
goto block_196;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_188);
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_212 = x_207;
} else {
 lean_dec_ref(x_207);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_208, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_208, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_215 = x_208;
} else {
 lean_dec_ref(x_208);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
if (lean_is_scalar(x_212)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_212;
}
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_211);
return x_217;
}
}
}
block_196:
{
lean_object* x_194; lean_object* x_195; 
if (lean_is_scalar(x_191)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_191;
}
lean_ctor_set(x_194, 0, x_189);
lean_ctor_set(x_194, 1, x_192);
if (lean_is_scalar(x_188)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_188;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_218 = lean_ctor_get(x_185, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_219 = x_185;
} else {
 lean_dec_ref(x_185);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_186, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_186, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_222 = x_186;
} else {
 lean_dec_ref(x_186);
 x_222 = lean_box(0);
}
x_228 = lean_ctor_get(x_221, 0);
lean_inc_ref(x_228);
lean_dec(x_221);
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_array_get_size(x_228);
x_231 = lean_nat_dec_lt(x_229, x_230);
if (x_231 == 0)
{
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec_ref(x_183);
x_223 = x_3;
x_224 = x_218;
goto block_227;
}
else
{
uint8_t x_232; 
x_232 = lean_nat_dec_le(x_230, x_230);
if (x_232 == 0)
{
lean_dec(x_230);
lean_dec_ref(x_228);
lean_dec_ref(x_183);
x_223 = x_3;
x_224 = x_218;
goto block_227;
}
else
{
lean_object* x_233; lean_object* x_234; size_t x_235; size_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_233 = lean_alloc_closure((void*)(l_Lake_Job_await___redArg___lam__0___boxed), 4, 0);
x_234 = lean_box(0);
x_235 = 0;
x_236 = lean_usize_of_nat(x_230);
lean_dec(x_230);
x_237 = l_Array_foldlMUnsafe_fold___redArg(x_183, x_233, x_228, x_235, x_236, x_234);
x_238 = lean_apply_2(x_237, x_3, x_218);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_223 = x_241;
x_224 = x_240;
goto block_227;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_219);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_243 = x_238;
} else {
 lean_dec_ref(x_238);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_239, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_239, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_246 = x_239;
} else {
 lean_dec_ref(x_239);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
if (lean_is_scalar(x_243)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_243;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_242);
return x_248;
}
}
}
block_227:
{
lean_object* x_225; lean_object* x_226; 
if (lean_is_scalar(x_222)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_222;
}
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_223);
if (lean_is_scalar(x_219)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_219;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Job_await___redArg___lam__0(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lake_BuildTrace_mix(x_1, x_16);
x_18 = lean_apply_1(x_2, x_14);
lean_ctor_set(x_13, 1, x_17);
x_19 = 1;
x_20 = l_IO_FS_withIsolatedStreams___redArg(x_3, x_4, x_5, x_18, x_19);
x_21 = lean_apply_7(x_20, x_6, x_7, x_8, x_9, x_10, x_13, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_27 = x_22;
} else {
 lean_dec_ref(x_22);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_35 = lean_string_utf8_byte_size(x_28);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_41 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_42 = l_Substring_takeWhileAux(x_28, x_35, x_41, x_36);
x_43 = l_Substring_takeRightWhileAux(x_28, x_42, x_41, x_35);
x_44 = lean_string_utf8_extract(x_28, x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_28);
x_45 = lean_string_append(x_40, x_44);
lean_dec_ref(x_44);
x_46 = 1;
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = lean_array_push(x_39, x_47);
lean_ctor_set(x_26, 0, x_48);
x_30 = x_26;
x_31 = x_24;
goto block_34;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_26, 0);
x_50 = lean_ctor_get_uint8(x_26, sizeof(void*)*2);
x_51 = lean_ctor_get(x_26, 1);
lean_inc(x_51);
lean_inc(x_49);
lean_dec(x_26);
x_52 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_53 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_54 = l_Substring_takeWhileAux(x_28, x_35, x_53, x_36);
x_55 = l_Substring_takeRightWhileAux(x_28, x_54, x_53, x_35);
x_56 = lean_string_utf8_extract(x_28, x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_28);
x_57 = lean_string_append(x_52, x_56);
lean_dec_ref(x_56);
x_58 = 1;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_push(x_49, x_59);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_50);
x_30 = x_61;
x_31 = x_24;
goto block_34;
}
}
else
{
lean_dec(x_35);
lean_dec(x_28);
x_30 = x_26;
x_31 = x_24;
goto block_34;
}
block_34:
{
lean_object* x_32; lean_object* x_33; 
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
if (lean_is_scalar(x_25)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_25;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_21);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_21, 0);
lean_dec(x_63);
x_64 = !lean_is_exclusive(x_22);
if (x_64 == 0)
{
return x_21;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_22, 0);
x_66 = lean_ctor_get(x_22, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_22);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_21, 0, x_67);
return x_21;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_21, 1);
lean_inc(x_68);
lean_dec(x_21);
x_69 = lean_ctor_get(x_22, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_22, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_71 = x_22;
} else {
 lean_dec_ref(x_22);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
}
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
lean_inc(x_74);
lean_dec(x_13);
x_77 = l_Lake_BuildTrace_mix(x_1, x_76);
x_78 = lean_apply_1(x_2, x_14);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_74);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_75);
x_80 = 1;
x_81 = l_IO_FS_withIsolatedStreams___redArg(x_3, x_4, x_5, x_78, x_80);
x_82 = lean_apply_7(x_81, x_6, x_7, x_8, x_9, x_10, x_79, x_12);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_86 = x_82;
} else {
 lean_dec_ref(x_82);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_88 = x_83;
} else {
 lean_dec_ref(x_83);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_96 = lean_string_utf8_byte_size(x_89);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_eq(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_99 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_99);
x_100 = lean_ctor_get_uint8(x_87, sizeof(void*)*2);
x_101 = lean_ctor_get(x_87, 1);
lean_inc_ref(x_101);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_102 = x_87;
} else {
 lean_dec_ref(x_87);
 x_102 = lean_box(0);
}
x_103 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_104 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_105 = l_Substring_takeWhileAux(x_89, x_96, x_104, x_97);
x_106 = l_Substring_takeRightWhileAux(x_89, x_105, x_104, x_96);
x_107 = lean_string_utf8_extract(x_89, x_105, x_106);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_89);
x_108 = lean_string_append(x_103, x_107);
lean_dec_ref(x_107);
x_109 = 1;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_push(x_99, x_110);
if (lean_is_scalar(x_102)) {
 x_112 = lean_alloc_ctor(0, 2, 1);
} else {
 x_112 = x_102;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_101);
lean_ctor_set_uint8(x_112, sizeof(void*)*2, x_100);
x_91 = x_112;
x_92 = x_85;
goto block_95;
}
else
{
lean_dec(x_96);
lean_dec(x_89);
x_91 = x_87;
x_92 = x_85;
goto block_95;
}
block_95:
{
lean_object* x_93; lean_object* x_94; 
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
if (lean_is_scalar(x_86)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_86;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_82, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_114 = x_82;
} else {
 lean_dec_ref(x_82);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_83, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_83, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_117 = x_83;
} else {
 lean_dec_ref(x_83);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_120 = !lean_is_exclusive(x_11);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_11);
lean_ctor_set(x_121, 1, x_12);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_11, 0);
x_123 = lean_ctor_get(x_11, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_11);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_12);
return x_125;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 2);
lean_dec(x_22);
lean_inc(x_17);
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_17);
lean_inc(x_17);
lean_inc(x_19);
x_24 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_17);
lean_inc_ref(x_23);
lean_inc(x_19);
x_25 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_25, 0, x_19);
lean_closure_set(x_25, 1, x_23);
lean_inc(x_17);
lean_inc(x_19);
lean_inc_ref(x_18);
x_26 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_26, 0, x_18);
lean_closure_set(x_26, 1, x_19);
lean_closure_set(x_26, 2, x_17);
x_27 = l_Lake_EStateT_instFunctor___redArg(x_18);
lean_inc(x_19);
x_28 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_28, 0, x_19);
lean_ctor_set(x_15, 4, x_24);
lean_ctor_set(x_15, 3, x_25);
lean_ctor_set(x_15, 2, x_26);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_27);
lean_ctor_set(x_13, 1, x_23);
x_29 = l_ReaderT_instMonad___redArg(x_13);
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = l_ReaderT_instMonad___redArg(x_31);
x_33 = l_Lake_EquipT_instMonad___redArg(x_32);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = l_Lake_Job_async___redArg___closed__7;
x_38 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_38, 0, x_19);
lean_closure_set(x_38, 1, x_17);
x_39 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__0), 12, 10);
lean_closure_set(x_44, 0, x_11);
lean_closure_set(x_44, 1, x_3);
lean_closure_set(x_44, 2, x_33);
lean_closure_set(x_44, 3, x_43);
lean_closure_set(x_44, 4, x_37);
lean_closure_set(x_44, 5, x_6);
lean_closure_set(x_44, 6, x_7);
lean_closure_set(x_44, 7, x_8);
lean_closure_set(x_44, 8, x_9);
lean_closure_set(x_44, 9, x_10);
x_45 = lean_io_map_task(x_44, x_35, x_4, x_5, x_12);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_47);
lean_ctor_set(x_45, 0, x_2);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_54 = l_Lake_Job_async___redArg___closed__7;
x_55 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_55, 0, x_19);
lean_closure_set(x_55, 1, x_17);
x_56 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_59);
x_61 = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__0), 12, 10);
lean_closure_set(x_61, 0, x_11);
lean_closure_set(x_61, 1, x_3);
lean_closure_set(x_61, 2, x_33);
lean_closure_set(x_61, 3, x_60);
lean_closure_set(x_61, 4, x_54);
lean_closure_set(x_61, 5, x_6);
lean_closure_set(x_61, 6, x_7);
lean_closure_set(x_61, 7, x_8);
lean_closure_set(x_61, 8, x_9);
lean_closure_set(x_61, 9, x_10);
x_62 = lean_io_map_task(x_61, x_51, x_4, x_5, x_12);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_1);
lean_ctor_set(x_66, 2, x_52);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_53);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_68 = lean_ctor_get(x_13, 1);
x_69 = lean_ctor_get(x_15, 0);
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_15);
lean_inc(x_68);
lean_inc(x_70);
x_71 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_68);
lean_inc(x_68);
lean_inc(x_70);
x_72 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_72, 0, x_70);
lean_closure_set(x_72, 1, x_68);
lean_inc_ref(x_71);
lean_inc(x_70);
x_73 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_73, 0, x_70);
lean_closure_set(x_73, 1, x_71);
lean_inc(x_68);
lean_inc(x_70);
lean_inc_ref(x_69);
x_74 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_74, 0, x_69);
lean_closure_set(x_74, 1, x_70);
lean_closure_set(x_74, 2, x_68);
x_75 = l_Lake_EStateT_instFunctor___redArg(x_69);
lean_inc(x_70);
x_76 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_76, 0, x_70);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set(x_13, 1, x_71);
lean_ctor_set(x_13, 0, x_77);
x_78 = l_ReaderT_instMonad___redArg(x_13);
x_79 = l_ReaderT_instMonad___redArg(x_78);
x_80 = l_ReaderT_instMonad___redArg(x_79);
x_81 = l_ReaderT_instMonad___redArg(x_80);
x_82 = l_Lake_EquipT_instMonad___redArg(x_81);
x_83 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_86 = x_2;
} else {
 lean_dec_ref(x_2);
 x_86 = lean_box(0);
}
x_87 = l_Lake_Job_async___redArg___closed__7;
x_88 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_88, 0, x_70);
lean_closure_set(x_88, 1, x_68);
x_89 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_89, 0, x_88);
x_90 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_91, 0, x_90);
x_92 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_92, 0, x_91);
x_93 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_93, 0, x_92);
x_94 = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__0), 12, 10);
lean_closure_set(x_94, 0, x_11);
lean_closure_set(x_94, 1, x_3);
lean_closure_set(x_94, 2, x_82);
lean_closure_set(x_94, 3, x_93);
lean_closure_set(x_94, 4, x_87);
lean_closure_set(x_94, 5, x_6);
lean_closure_set(x_94, 6, x_7);
lean_closure_set(x_94, 7, x_8);
lean_closure_set(x_94, 8, x_9);
lean_closure_set(x_94, 9, x_10);
x_95 = lean_io_map_task(x_94, x_83, x_4, x_5, x_12);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_99 = lean_alloc_ctor(0, 3, 1);
} else {
 x_99 = x_86;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_1);
lean_ctor_set(x_99, 2, x_84);
lean_ctor_set_uint8(x_99, sizeof(void*)*3, x_85);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_101 = lean_ctor_get(x_13, 0);
x_102 = lean_ctor_get(x_13, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_13);
x_103 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
lean_inc(x_102);
lean_inc(x_104);
x_106 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_106, 0, x_104);
lean_closure_set(x_106, 1, x_102);
lean_inc(x_102);
lean_inc(x_104);
x_107 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_107, 0, x_104);
lean_closure_set(x_107, 1, x_102);
lean_inc_ref(x_106);
lean_inc(x_104);
x_108 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_108, 0, x_104);
lean_closure_set(x_108, 1, x_106);
lean_inc(x_102);
lean_inc(x_104);
lean_inc_ref(x_103);
x_109 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_109, 0, x_103);
lean_closure_set(x_109, 1, x_104);
lean_closure_set(x_109, 2, x_102);
x_110 = l_Lake_EStateT_instFunctor___redArg(x_103);
lean_inc(x_104);
x_111 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_111, 0, x_104);
if (lean_is_scalar(x_105)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_105;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_108);
lean_ctor_set(x_112, 4, x_107);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
x_114 = l_ReaderT_instMonad___redArg(x_113);
x_115 = l_ReaderT_instMonad___redArg(x_114);
x_116 = l_ReaderT_instMonad___redArg(x_115);
x_117 = l_ReaderT_instMonad___redArg(x_116);
x_118 = l_Lake_EquipT_instMonad___redArg(x_117);
x_119 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_120);
x_121 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_122 = x_2;
} else {
 lean_dec_ref(x_2);
 x_122 = lean_box(0);
}
x_123 = l_Lake_Job_async___redArg___closed__7;
x_124 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_124, 0, x_104);
lean_closure_set(x_124, 1, x_102);
x_125 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_125, 0, x_124);
x_126 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_126, 0, x_125);
x_127 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_127, 0, x_126);
x_128 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_128, 0, x_127);
x_129 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_129, 0, x_128);
x_130 = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__0), 12, 10);
lean_closure_set(x_130, 0, x_11);
lean_closure_set(x_130, 1, x_3);
lean_closure_set(x_130, 2, x_118);
lean_closure_set(x_130, 3, x_129);
lean_closure_set(x_130, 4, x_123);
lean_closure_set(x_130, 5, x_6);
lean_closure_set(x_130, 6, x_7);
lean_closure_set(x_130, 7, x_8);
lean_closure_set(x_130, 8, x_9);
lean_closure_set(x_130, 9, x_10);
x_131 = lean_io_map_task(x_130, x_119, x_4, x_5, x_12);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_135 = lean_alloc_ctor(0, 3, 1);
} else {
 x_135 = x_122;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_1);
lean_ctor_set(x_135, 2, x_120);
lean_ctor_set_uint8(x_135, sizeof(void*)*3, x_121);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_Job_mapM___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_mapM___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l_Lake_Job_mapM(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindSync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_Job_mapM___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindSync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_Job_mapM___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindSync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindSync___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindSync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l_Lake_Job_bindSync(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = l_Lake_JobState_merge(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_6);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_7);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_7);
lean_ctor_set(x_2, 1, x_11);
return x_2;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_13);
x_14 = l_Lake_JobState_merge(x_1, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*2);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_17);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_18 = x_13;
} else {
 lean_dec_ref(x_13);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 1);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_24);
lean_inc(x_23);
x_25 = l_Lake_JobState_merge(x_1, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*2);
lean_dec_ref(x_25);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = lean_array_get_size(x_24);
lean_dec_ref(x_24);
x_31 = lean_nat_add(x_30, x_22);
lean_dec(x_22);
lean_dec(x_30);
lean_ctor_set(x_23, 0, x_26);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_27);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_array_get_size(x_24);
lean_dec_ref(x_24);
x_34 = lean_nat_add(x_33, x_22);
lean_dec(x_22);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_27);
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_38);
lean_inc(x_37);
x_39 = l_Lake_JobState_merge(x_1, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
x_44 = lean_array_get_size(x_38);
lean_dec_ref(x_38);
x_45 = lean_nat_add(x_44, x_36);
lean_dec(x_36);
lean_dec(x_44);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 1);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_21; 
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 0);
lean_inc(x_40);
lean_dec_ref(x_12);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_39, 1);
x_43 = l_Lake_BuildTrace_mix(x_1, x_42);
x_44 = lean_apply_1(x_2, x_40);
lean_ctor_set(x_39, 1, x_43);
x_45 = 1;
x_46 = l_IO_FS_withIsolatedStreams___redArg(x_3, x_4, x_5, x_44, x_45);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = lean_apply_7(x_46, x_6, x_7, x_8, x_9, x_10, x_39, x_13);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_string_utf8_byte_size(x_52);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_nat_dec_eq(x_54, x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_60 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_61 = l_Substring_takeWhileAux(x_52, x_54, x_60, x_55);
x_62 = l_Substring_takeRightWhileAux(x_52, x_61, x_60, x_54);
x_63 = lean_string_utf8_extract(x_52, x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_52);
x_64 = lean_string_append(x_59, x_63);
lean_dec_ref(x_63);
x_65 = 1;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_67 = lean_box(0);
x_68 = lean_array_push(x_58, x_66);
lean_ctor_set(x_51, 0, x_68);
x_69 = l_Lake_Job_bindM___redArg___lam__1(x_53, x_67, x_6, x_7, x_8, x_9, x_10, x_51, x_50);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = x_69;
goto block_38;
}
else
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_70 = lean_ctor_get(x_51, 0);
x_71 = lean_ctor_get_uint8(x_51, sizeof(void*)*2);
x_72 = lean_ctor_get(x_51, 1);
lean_inc(x_72);
lean_inc(x_70);
lean_dec(x_51);
x_73 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_74 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_75 = l_Substring_takeWhileAux(x_52, x_54, x_74, x_55);
x_76 = l_Substring_takeRightWhileAux(x_52, x_75, x_74, x_54);
x_77 = lean_string_utf8_extract(x_52, x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_52);
x_78 = lean_string_append(x_73, x_77);
lean_dec_ref(x_77);
x_79 = 1;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_box(0);
x_82 = lean_array_push(x_70, x_80);
x_83 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_72);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_71);
x_84 = l_Lake_Job_bindM___redArg___lam__1(x_53, x_81, x_6, x_7, x_8, x_9, x_10, x_83, x_50);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = x_84;
goto block_38;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_54);
lean_dec(x_52);
x_85 = lean_box(0);
x_86 = l_Lake_Job_bindM___redArg___lam__1(x_53, x_85, x_6, x_7, x_8, x_9, x_10, x_51, x_50);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = x_86;
goto block_38;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_87 = lean_ctor_get(x_47, 1);
lean_inc(x_87);
lean_dec(x_47);
x_88 = lean_ctor_get(x_48, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_48, 1);
lean_inc(x_89);
lean_dec(x_48);
x_14 = x_88;
x_15 = x_89;
x_16 = x_87;
goto block_20;
}
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_39, 0);
x_91 = lean_ctor_get_uint8(x_39, sizeof(void*)*2);
x_92 = lean_ctor_get(x_39, 1);
lean_inc(x_92);
lean_inc(x_90);
lean_dec(x_39);
x_93 = l_Lake_BuildTrace_mix(x_1, x_92);
x_94 = lean_apply_1(x_2, x_40);
x_95 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*2, x_91);
x_96 = 1;
x_97 = l_IO_FS_withIsolatedStreams___redArg(x_3, x_4, x_5, x_94, x_96);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_98 = lean_apply_7(x_97, x_6, x_7, x_8, x_9, x_10, x_95, x_13);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_100, 1);
lean_inc(x_104);
lean_dec(x_100);
x_105 = lean_string_utf8_byte_size(x_103);
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_108 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_108);
x_109 = lean_ctor_get_uint8(x_102, sizeof(void*)*2);
x_110 = lean_ctor_get(x_102, 1);
lean_inc_ref(x_110);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_111 = x_102;
} else {
 lean_dec_ref(x_102);
 x_111 = lean_box(0);
}
x_112 = l_Lake_Job_async___redArg___lam__0___closed__0;
x_113 = l_Lake_Job_async___redArg___lam__0___closed__1;
x_114 = l_Substring_takeWhileAux(x_103, x_105, x_113, x_106);
x_115 = l_Substring_takeRightWhileAux(x_103, x_114, x_113, x_105);
x_116 = lean_string_utf8_extract(x_103, x_114, x_115);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_103);
x_117 = lean_string_append(x_112, x_116);
lean_dec_ref(x_116);
x_118 = 1;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_box(0);
x_121 = lean_array_push(x_108, x_119);
if (lean_is_scalar(x_111)) {
 x_122 = lean_alloc_ctor(0, 2, 1);
} else {
 x_122 = x_111;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_110);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_109);
x_123 = l_Lake_Job_bindM___redArg___lam__1(x_104, x_120, x_6, x_7, x_8, x_9, x_10, x_122, x_101);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = x_123;
goto block_38;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_105);
lean_dec(x_103);
x_124 = lean_box(0);
x_125 = l_Lake_Job_bindM___redArg___lam__1(x_104, x_124, x_6, x_7, x_8, x_9, x_10, x_102, x_101);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = x_125;
goto block_38;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_126 = lean_ctor_get(x_98, 1);
lean_inc(x_126);
lean_dec(x_98);
x_127 = lean_ctor_get(x_99, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_99, 1);
lean_inc(x_128);
lean_dec(x_99);
x_14 = x_127;
x_15 = x_128;
x_16 = x_126;
goto block_20;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_129 = !lean_is_exclusive(x_12);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_task_pure(x_12);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_13);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_12, 0);
x_133 = lean_ctor_get(x_12, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_12);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_task_pure(x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_13);
return x_136;
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_task_pure(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
block_38:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_27);
lean_dec(x_23);
x_28 = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__0), 2, 1);
lean_closure_set(x_28, 0, x_26);
x_29 = 1;
x_30 = lean_task_map(x_28, x_27, x_11, x_29);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_dec(x_22);
x_33 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_33);
lean_dec(x_23);
x_34 = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__0), 2, 1);
lean_closure_set(x_34, 0, x_32);
x_35 = 1;
x_36 = lean_task_map(x_34, x_33, x_11, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lake_instMonadStateOfLogJobM___closed__0;
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 4);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 3);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 2);
lean_dec(x_22);
lean_inc(x_17);
lean_inc(x_19);
x_23 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_23, 0, x_19);
lean_closure_set(x_23, 1, x_17);
lean_inc(x_17);
lean_inc(x_19);
x_24 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_24, 0, x_19);
lean_closure_set(x_24, 1, x_17);
lean_inc_ref(x_23);
lean_inc(x_19);
x_25 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_25, 0, x_19);
lean_closure_set(x_25, 1, x_23);
lean_inc(x_17);
lean_inc(x_19);
lean_inc_ref(x_18);
x_26 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_26, 0, x_18);
lean_closure_set(x_26, 1, x_19);
lean_closure_set(x_26, 2, x_17);
x_27 = l_Lake_EStateT_instFunctor___redArg(x_18);
lean_inc(x_19);
x_28 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_28, 0, x_19);
lean_ctor_set(x_15, 4, x_24);
lean_ctor_set(x_15, 3, x_25);
lean_ctor_set(x_15, 2, x_26);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_27);
lean_ctor_set(x_13, 1, x_23);
x_29 = l_ReaderT_instMonad___redArg(x_13);
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = l_ReaderT_instMonad___redArg(x_30);
x_32 = l_ReaderT_instMonad___redArg(x_31);
x_33 = l_Lake_EquipT_instMonad___redArg(x_32);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = l_Lake_Job_async___redArg___closed__7;
x_38 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_38, 0, x_19);
lean_closure_set(x_38, 1, x_17);
x_39 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_42);
lean_inc(x_4);
x_44 = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2), 13, 11);
lean_closure_set(x_44, 0, x_11);
lean_closure_set(x_44, 1, x_3);
lean_closure_set(x_44, 2, x_33);
lean_closure_set(x_44, 3, x_43);
lean_closure_set(x_44, 4, x_37);
lean_closure_set(x_44, 5, x_6);
lean_closure_set(x_44, 6, x_7);
lean_closure_set(x_44, 7, x_8);
lean_closure_set(x_44, 8, x_9);
lean_closure_set(x_44, 9, x_10);
lean_closure_set(x_44, 10, x_4);
x_45 = lean_io_bind_task(x_35, x_44, x_4, x_5, x_12);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_47);
lean_ctor_set(x_45, 0, x_2);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_2);
x_54 = l_Lake_Job_async___redArg___closed__7;
x_55 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_55, 0, x_19);
lean_closure_set(x_55, 1, x_17);
x_56 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_56);
x_58 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_57);
x_59 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_59, 0, x_58);
x_60 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_60, 0, x_59);
lean_inc(x_4);
x_61 = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2), 13, 11);
lean_closure_set(x_61, 0, x_11);
lean_closure_set(x_61, 1, x_3);
lean_closure_set(x_61, 2, x_33);
lean_closure_set(x_61, 3, x_60);
lean_closure_set(x_61, 4, x_54);
lean_closure_set(x_61, 5, x_6);
lean_closure_set(x_61, 6, x_7);
lean_closure_set(x_61, 7, x_8);
lean_closure_set(x_61, 8, x_9);
lean_closure_set(x_61, 9, x_10);
lean_closure_set(x_61, 10, x_4);
x_62 = lean_io_bind_task(x_51, x_61, x_4, x_5, x_12);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_1);
lean_ctor_set(x_66, 2, x_52);
lean_ctor_set_uint8(x_66, sizeof(void*)*3, x_53);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_68 = lean_ctor_get(x_13, 1);
x_69 = lean_ctor_get(x_15, 0);
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_15);
lean_inc(x_68);
lean_inc(x_70);
x_71 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_68);
lean_inc(x_68);
lean_inc(x_70);
x_72 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_72, 0, x_70);
lean_closure_set(x_72, 1, x_68);
lean_inc_ref(x_71);
lean_inc(x_70);
x_73 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_73, 0, x_70);
lean_closure_set(x_73, 1, x_71);
lean_inc(x_68);
lean_inc(x_70);
lean_inc_ref(x_69);
x_74 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_74, 0, x_69);
lean_closure_set(x_74, 1, x_70);
lean_closure_set(x_74, 2, x_68);
x_75 = l_Lake_EStateT_instFunctor___redArg(x_69);
lean_inc(x_70);
x_76 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_76, 0, x_70);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set(x_13, 1, x_71);
lean_ctor_set(x_13, 0, x_77);
x_78 = l_ReaderT_instMonad___redArg(x_13);
x_79 = l_ReaderT_instMonad___redArg(x_78);
x_80 = l_ReaderT_instMonad___redArg(x_79);
x_81 = l_ReaderT_instMonad___redArg(x_80);
x_82 = l_Lake_EquipT_instMonad___redArg(x_81);
x_83 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_84);
x_85 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_86 = x_2;
} else {
 lean_dec_ref(x_2);
 x_86 = lean_box(0);
}
x_87 = l_Lake_Job_async___redArg___closed__7;
x_88 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_88, 0, x_70);
lean_closure_set(x_88, 1, x_68);
x_89 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_89, 0, x_88);
x_90 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_90, 0, x_89);
x_91 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_91, 0, x_90);
x_92 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_92, 0, x_91);
x_93 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_93, 0, x_92);
lean_inc(x_4);
x_94 = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2), 13, 11);
lean_closure_set(x_94, 0, x_11);
lean_closure_set(x_94, 1, x_3);
lean_closure_set(x_94, 2, x_82);
lean_closure_set(x_94, 3, x_93);
lean_closure_set(x_94, 4, x_87);
lean_closure_set(x_94, 5, x_6);
lean_closure_set(x_94, 6, x_7);
lean_closure_set(x_94, 7, x_8);
lean_closure_set(x_94, 8, x_9);
lean_closure_set(x_94, 9, x_10);
lean_closure_set(x_94, 10, x_4);
x_95 = lean_io_bind_task(x_83, x_94, x_4, x_5, x_12);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_99 = lean_alloc_ctor(0, 3, 1);
} else {
 x_99 = x_86;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_1);
lean_ctor_set(x_99, 2, x_84);
lean_ctor_set_uint8(x_99, sizeof(void*)*3, x_85);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_101 = lean_ctor_get(x_13, 0);
x_102 = lean_ctor_get(x_13, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_13);
x_103 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
lean_inc(x_102);
lean_inc(x_104);
x_106 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(x_106, 0, x_104);
lean_closure_set(x_106, 1, x_102);
lean_inc(x_102);
lean_inc(x_104);
x_107 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_107, 0, x_104);
lean_closure_set(x_107, 1, x_102);
lean_inc_ref(x_106);
lean_inc(x_104);
x_108 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(x_108, 0, x_104);
lean_closure_set(x_108, 1, x_106);
lean_inc(x_102);
lean_inc(x_104);
lean_inc_ref(x_103);
x_109 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(x_109, 0, x_103);
lean_closure_set(x_109, 1, x_104);
lean_closure_set(x_109, 2, x_102);
x_110 = l_Lake_EStateT_instFunctor___redArg(x_103);
lean_inc(x_104);
x_111 = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(x_111, 0, x_104);
if (lean_is_scalar(x_105)) {
 x_112 = lean_alloc_ctor(0, 5, 0);
} else {
 x_112 = x_105;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_108);
lean_ctor_set(x_112, 4, x_107);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
x_114 = l_ReaderT_instMonad___redArg(x_113);
x_115 = l_ReaderT_instMonad___redArg(x_114);
x_116 = l_ReaderT_instMonad___redArg(x_115);
x_117 = l_ReaderT_instMonad___redArg(x_116);
x_118 = l_Lake_EquipT_instMonad___redArg(x_117);
x_119 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_120);
x_121 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_122 = x_2;
} else {
 lean_dec_ref(x_2);
 x_122 = lean_box(0);
}
x_123 = l_Lake_Job_async___redArg___closed__7;
x_124 = lean_alloc_closure((void*)(l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__3), 7, 2);
lean_closure_set(x_124, 0, x_104);
lean_closure_set(x_124, 1, x_102);
x_125 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_125, 0, x_124);
x_126 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_126, 0, x_125);
x_127 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_127, 0, x_126);
x_128 = lean_alloc_closure((void*)(l_ReaderT_tryFinally___redArg___lam__1), 6, 1);
lean_closure_set(x_128, 0, x_127);
x_129 = lean_alloc_closure((void*)(l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_129, 0, x_128);
lean_inc(x_4);
x_130 = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2), 13, 11);
lean_closure_set(x_130, 0, x_11);
lean_closure_set(x_130, 1, x_3);
lean_closure_set(x_130, 2, x_118);
lean_closure_set(x_130, 3, x_129);
lean_closure_set(x_130, 4, x_123);
lean_closure_set(x_130, 5, x_6);
lean_closure_set(x_130, 6, x_7);
lean_closure_set(x_130, 7, x_8);
lean_closure_set(x_130, 8, x_9);
lean_closure_set(x_130, 9, x_10);
lean_closure_set(x_130, 10, x_4);
x_131 = lean_io_bind_task(x_119, x_130, x_4, x_5, x_12);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_135 = lean_alloc_ctor(0, 3, 1);
} else {
 x_135 = x_122;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_1);
lean_ctor_set(x_135, 2, x_120);
lean_ctor_set_uint8(x_135, sizeof(void*)*3, x_121);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lake_Job_bindM___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_Job_bindM___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindM___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l_Lake_Job_bindM(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
x_11 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lake_Job_bindAsync___redArg___lam__0), 9, 1);
lean_closure_set(x_13, 0, x_3);
x_14 = l_Lake_Job_bindM___redArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Lake_Job_bindAsync___redArg___lam__0), 9, 1);
lean_closure_set(x_15, 0, x_5);
x_16 = l_Lake_Job_bindM___redArg(x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_Job_bindAsync___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindAsync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l_Lake_Job_bindAsync(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_task_map(x_7, x_6, x_3, x_4);
return x_8;
}
}
static lean_object* _init_l_Lake_Job_zipResultWith___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_box(x_6);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_11);
x_13 = 1;
x_14 = lean_task_bind(x_8, x_12, x_5, x_13);
x_15 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_16 = 0;
lean_ctor_set(x_3, 2, x_15);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_14);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_16);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(x_6);
lean_inc(x_5);
x_19 = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_18);
x_20 = 1;
x_21 = lean_task_bind(x_17, x_19, x_5, x_20);
x_22 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_dec(x_13);
x_14 = lean_box(x_9);
lean_inc(x_8);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_8);
lean_closure_set(x_15, 3, x_14);
x_16 = 1;
x_17 = lean_task_bind(x_11, x_15, x_8, x_16);
x_18 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_19 = 0;
lean_ctor_set(x_6, 2, x_18);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_17);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_box(x_9);
lean_inc(x_8);
x_22 = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_22, 0, x_7);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_8);
lean_closure_set(x_22, 3, x_21);
x_23 = 1;
x_24 = lean_task_bind(x_20, x_22, x_8, x_23);
x_25 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_Lake_Job_zipResultWith___redArg___lam__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lake_Job_zipResultWith___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
x_11 = l_Lake_Job_zipResultWith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_apply_2(x_2, x_10, x_13);
x_16 = l_Lake_JobState_merge(x_11, x_14);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
x_19 = lean_apply_2(x_2, x_10, x_17);
x_20 = l_Lake_JobState_merge(x_11, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec_ref(x_3);
x_24 = lean_unsigned_to_nat(0u);
x_4 = x_22;
x_5 = x_24;
x_6 = x_23;
goto block_9;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_dec_ref(x_3);
x_4 = x_25;
x_5 = x_26;
x_6 = x_27;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lake_JobState_merge(x_4, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_task_map(x_7, x_6, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = lean_box(x_6);
lean_inc(x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_5);
lean_closure_set(x_12, 3, x_11);
x_13 = 1;
x_14 = lean_task_bind(x_8, x_12, x_5, x_13);
x_15 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_16 = 0;
lean_ctor_set(x_3, 2, x_15);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_14);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_16);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(x_6);
lean_inc(x_5);
x_19 = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_18);
x_20 = 1;
x_21 = lean_task_bind(x_17, x_19, x_5, x_20);
x_22 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_dec(x_13);
x_14 = lean_box(x_9);
lean_inc(x_8);
x_15 = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_8);
lean_closure_set(x_15, 3, x_14);
x_16 = 1;
x_17 = lean_task_bind(x_11, x_15, x_8, x_16);
x_18 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_19 = 0;
lean_ctor_set(x_6, 2, x_18);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_17);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_19);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = lean_box(x_9);
lean_inc(x_8);
x_22 = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_22, 0, x_7);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_8);
lean_closure_set(x_22, 3, x_21);
x_23 = 1;
x_24 = lean_task_bind(x_20, x_22, x_8, x_23);
x_25 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_Lake_Job_zipWith___redArg___lam__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lake_Job_zipWith___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
x_11 = l_Lake_Job_zipWith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec_ref(x_2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
lean_inc(x_17);
x_21 = l_Lake_JobState_merge(x_17, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*2);
lean_dec_ref(x_21);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
lean_ctor_set(x_17, 0, x_22);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_23);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_dec(x_3);
lean_inc(x_17);
x_29 = l_Lake_JobState_merge(x_17, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get_uint8(x_29, sizeof(void*)*2);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_32);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_33 = x_17;
} else {
 lean_dec_ref(x_17);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 1);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_3, 1);
lean_inc(x_37);
lean_dec_ref(x_3);
x_4 = x_36;
x_5 = x_37;
goto block_15;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec_ref(x_2);
x_39 = lean_ctor_get(x_3, 1);
lean_inc(x_39);
lean_dec_ref(x_3);
x_4 = x_38;
x_5 = x_39;
goto block_15;
}
block_15:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
lean_inc_ref(x_4);
x_6 = l_Lake_JobState_merge(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*2);
lean_dec_ref(x_6);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
lean_ctor_set(x_4, 0, x_7);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_8);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_task_map(x_6, x_5, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_task_bind(x_4, x_9, x_6, x_7);
x_11 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_12 = 0;
lean_ctor_set(x_1, 2, x_11);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set_uint8(x_1, sizeof(void*)*3, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
x_19 = lean_task_bind(x_13, x_18, x_15, x_16);
x_20 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_14);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Job_add___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lake_Job_add___redArg___lam__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = l_Lake_JobState_merge(x_9, x_11);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = l_Lake_JobState_merge(x_9, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_dec_ref(x_3);
x_4 = x_19;
x_5 = x_20;
goto block_8;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec_ref(x_3);
x_4 = x_21;
x_5 = x_22;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_JobState_merge(x_4, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_task_map(x_6, x_5, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 2);
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = l_Lake_instDataKindUnit;
x_8 = lean_unsigned_to_nat(0u);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_task_bind(x_4, x_11, x_8, x_9);
x_13 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_14 = 0;
lean_ctor_set(x_1, 2, x_13);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set_uint8(x_1, sizeof(void*)*3, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lake_instDataKindUnit;
x_17 = lean_unsigned_to_nat(0u);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_task_bind(x_15, x_20, x_17, x_18);
x_22 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Job_mix___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lake_Job_mix___redArg___lam__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_Lake_Job_mix___redArg(x_8, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_mixList_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_array_mk(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec_ref(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = 0;
x_9 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___redArg(x_3, x_7, x_8, x_1);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_mixList_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldrTR___at___Lake_Job_mixList_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = l_Lake_Job_async___redArg___closed__8;
x_6 = 0;
x_7 = l_Lake_BuildTrace_nil(x_2);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_task_pure(x_9);
x_11 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
x_14 = l_List_foldrTR___at___Lake_Job_mixList_spec__0___redArg(x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Job_mixList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_mixList_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_Job_mix___redArg(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lake_Job_async___redArg___closed__8;
x_7 = 0;
x_8 = l_Lake_BuildTrace_nil(x_2);
x_9 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_task_pure(x_10);
x_12 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_13);
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_5, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
return x_14;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
return x_14;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_20 = l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___redArg(x_1, x_18, x_19, x_14);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Job_mixArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___redArg(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_Job_mixArray_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Job_mixArray___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Job_mixArray(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_12);
x_14 = l_Lake_JobState_merge(x_11, x_13);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_16);
x_18 = l_Lake_JobState_merge(x_15, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_24 = x_3;
} else {
 lean_dec_ref(x_3);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_22);
x_26 = l_Lake_JobState_merge(x_21, x_23);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_dec_ref(x_3);
x_4 = x_28;
x_5 = x_29;
goto block_8;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec_ref(x_2);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
lean_dec_ref(x_3);
x_4 = x_30;
x_5 = x_31;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_JobState_merge(x_4, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_task_map(x_6, x_5, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
size_t x_7; size_t x_8; lean_object* x_9; uint8_t x_10; 
x_7 = 1;
x_8 = lean_usize_sub(x_3, x_7);
x_9 = lean_array_uget(x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = lean_task_bind(x_11, x_17, x_14, x_15);
x_19 = l_Lake_Job_zipResultWith___redArg___closed__0;
lean_inc(x_1);
lean_ctor_set(x_9, 2, x_19);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_18);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_6);
x_3 = x_8;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_22);
lean_closure_set(x_25, 2, x_24);
x_26 = lean_task_bind(x_21, x_25, x_22, x_23);
x_27 = l_Lake_Job_zipResultWith___redArg___closed__0;
lean_inc(x_1);
x_28 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_1);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_6);
x_3 = x_8;
x_5 = x_28;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_collectList_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_array_mk(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_9 = 0;
x_10 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg(x_1, x_4, x_8, x_9, x_2);
lean_dec_ref(x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___Lake_Job_collectList_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldrTR___at___Lake_Job_collectList_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = l_Lake_Job_async___redArg___closed__8;
x_6 = 0;
x_7 = l_Lake_BuildTrace_nil(x_2);
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_task_pure(x_9);
x_11 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
x_14 = l_List_foldrTR___at___Lake_Job_collectList_spec__0___redArg(x_3, x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Job_collectList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldrMUnsafe_fold___at___List_foldrTR___at___Lake_Job_collectList_spec__0_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_array_push(x_9, x_12);
x_15 = l_Lake_JobState_merge(x_10, x_13);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_array_push(x_9, x_16);
x_19 = l_Lake_JobState_merge(x_10, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec_ref(x_3);
x_4 = x_21;
x_5 = x_22;
goto block_8;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_dec_ref(x_3);
x_4 = x_23;
x_5 = x_24;
goto block_8;
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lake_JobState_merge(x_4, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_task_map(x_6, x_5, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = lean_array_uget(x_2, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_14);
x_16 = lean_task_bind(x_8, x_15, x_12, x_13);
x_17 = l_Lake_Job_zipResultWith___redArg___closed__0;
lean_inc(x_1);
lean_ctor_set(x_5, 2, x_17);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_16);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
lean_dec(x_5);
x_22 = lean_array_uget(x_2, x_3);
x_23 = lean_unsigned_to_nat(0u);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_26, 0, x_22);
lean_closure_set(x_26, 1, x_23);
lean_closure_set(x_26, 2, x_25);
x_27 = lean_task_bind(x_21, x_26, x_23, x_24);
x_28 = l_Lake_Job_zipResultWith___redArg___closed__0;
lean_inc(x_1);
x_29 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*3, x_6);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_5 = x_29;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_3 = lean_box(0);
x_4 = lean_array_get_size(x_1);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lake_Job_async___redArg___closed__8;
x_8 = 0;
x_9 = l_Lake_BuildTrace_nil(x_2);
x_10 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_task_pure(x_11);
x_13 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_14);
x_16 = lean_nat_dec_lt(x_6, x_4);
if (x_16 == 0)
{
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_4, x_4);
if (x_17 == 0)
{
lean_dec(x_4);
return x_15;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_20 = l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg(x_3, x_1, x_18, x_19, x_15);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Job_collectArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___lam__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_Job_collectArray_spec__0(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Job_collectArray___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Job_collectArray(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mk___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
lean_ctor_set(x_4, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_18 = x_13;
} else {
 lean_dec_ref(x_13);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 1);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mk___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = lean_alloc_closure((void*)(l_Lake_BuildJob_mk___redArg___lam__0), 1, 0);
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = lean_task_map(x_5, x_3, x_7, x_8);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_BuildJob_mk___redArg___lam__0), 1, 0);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = lean_task_map(x_13, x_10, x_15, x_16);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_dec(x_5);
x_6 = lean_alloc_closure((void*)(l_Lake_BuildJob_mk___redArg___lam__0), 1, 0);
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = lean_task_map(x_6, x_4, x_8, x_9);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_14 = lean_alloc_closure((void*)(l_Lake_BuildJob_mk___redArg___lam__0), 1, 0);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(0u);
x_17 = 0;
x_18 = lean_task_map(x_14, x_11, x_16, x_17);
x_19 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*3, x_13);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_ofJob___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 1, x_5);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_10);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
x_18 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 1);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_ofJob(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = lean_alloc_closure((void*)(l_Lake_BuildJob_ofJob___lam__0), 1, 0);
x_6 = l_Lake_instDataKindUnit;
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = lean_task_map(x_5, x_3, x_7, x_8);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l_Lake_BuildJob_ofJob___lam__0), 1, 0);
x_14 = l_Lake_instDataKindUnit;
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = lean_task_map(x_13, x_10, x_15, x_16);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob___redArg(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildJob_toJob___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_toJob___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildJob_toJob(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildJob_nil___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Job_async___redArg___closed__9;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildJob_nil___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_BuildJob_nil___closed__0;
x_2 = lean_task_pure(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildJob_nil___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_3 = l_Lake_instDataKindUnit;
x_4 = l_Lake_BuildJob_nil___closed__1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildJob_nil() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_BuildJob_nil___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_pure___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_3 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_4 = l_Lake_Job_async___redArg___closed__9;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_task_pure(x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_pure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_5 = l_Lake_Job_async___redArg___closed__9;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_task_pure(x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_instPure___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_box(0);
x_4 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_5 = l_Lake_Job_async___redArg___closed__9;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_task_pure(x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_BuildJob_instPure() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildJob_instPure___lam__0), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_map___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_map___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = lean_alloc_closure((void*)(l_Lake_BuildJob_map___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = lean_task_map(x_7, x_5, x_8, x_9);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_BuildJob_map___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = lean_task_map(x_14, x_11, x_15, x_16);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_BuildJob_map___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = lean_task_map(x_9, x_7, x_10, x_11);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_16 = lean_alloc_closure((void*)(l_Lake_BuildJob_map___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_task_map(x_16, x_13, x_17, x_18);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_15);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_instFunctor___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = lean_alloc_closure((void*)(l_Lake_BuildJob_map___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_3);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = lean_task_map(x_8, x_6, x_10, x_11);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_16 = lean_alloc_closure((void*)(l_Lake_BuildJob_map___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_3);
x_17 = lean_box(0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = 0;
x_20 = lean_task_map(x_16, x_13, x_18, x_19);
x_21 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set_uint8(x_21, sizeof(void*)*3, x_15);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_instFunctor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Function_const___boxed), 4, 3);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, x_4);
x_7 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_6, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_BuildJob_instFunctor() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildJob_instFunctor___lam__1), 4, 0);
lean_inc_ref(x_1);
x_2 = lean_alloc_closure((void*)(l_Lake_BuildJob_instFunctor___lam__0), 5, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mapWithTrace___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_ctor_set(x_4, 1, x_10);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_12);
lean_dec(x_4);
x_15 = lean_apply_2(x_1, x_11, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_13);
lean_ctor_set(x_2, 1, x_18);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*2);
x_23 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_apply_2(x_1, x_20, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 1);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
return x_2;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mapWithTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = lean_alloc_closure((void*)(l_Lake_BuildJob_mapWithTrace___redArg___lam__0), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = lean_task_map(x_7, x_5, x_8, x_9);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_alloc_closure((void*)(l_Lake_BuildJob_mapWithTrace___redArg___lam__0), 2, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = lean_task_map(x_14, x_11, x_15, x_16);
x_18 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*3, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mapWithTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_dec(x_8);
x_9 = lean_alloc_closure((void*)(l_Lake_BuildJob_mapWithTrace___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = 0;
x_12 = lean_task_map(x_9, x_7, x_10, x_11);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_16 = lean_alloc_closure((void*)(l_Lake_BuildJob_mapWithTrace___redArg___lam__0), 2, 1);
lean_closure_set(x_16, 0, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = lean_task_map(x_16, x_13, x_17, x_18);
x_20 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_14);
lean_ctor_set_uint8(x_20, sizeof(void*)*3, x_15);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
x_11 = lean_apply_9(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_16, 1);
lean_dec(x_21);
lean_ctor_set(x_16, 1, x_19);
lean_ctor_set(x_12, 0, x_18);
return x_11;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_23);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_18);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get_uint8(x_26, sizeof(void*)*2);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_32 = x_26;
} else {
 lean_dec_ref(x_26);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 1);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_31);
lean_ctor_set(x_12, 1, x_33);
lean_ctor_set(x_12, 0, x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_38 = x_11;
} else {
 lean_dec_ref(x_11);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get_uint8(x_36, sizeof(void*)*2);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 1);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_38)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_38;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_11, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
return x_11;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_12, 0);
x_51 = lean_ctor_get(x_12, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_11, 0, x_52);
return x_11;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_ctor_get(x_12, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_12, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_56 = x_12;
} else {
 lean_dec_ref(x_12);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lake_BuildJob_bindSync___redArg___lam__0), 9, 1);
lean_closure_set(x_13, 0, x_3);
x_14 = l_Lake_Job_mapM___redArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Lake_BuildJob_bindSync___redArg___lam__0), 9, 1);
lean_closure_set(x_15, 0, x_5);
x_16 = l_Lake_Job_mapM___redArg(x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_BuildJob_bindSync___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindSync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l_Lake_BuildJob_bindSync(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
lean_inc_ref(x_10);
x_11 = lean_apply_9(x_1, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lake_BuildJob_bindAsync___redArg___lam__0), 9, 1);
lean_closure_set(x_13, 0, x_3);
x_14 = l_Lake_Job_bindM___redArg(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_closure((void*)(l_Lake_BuildJob_bindAsync___redArg___lam__0), 9, 1);
lean_closure_set(x_15, 0, x_5);
x_16 = l_Lake_Job_bindM___redArg(x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
x_14 = l_Lake_BuildJob_bindAsync___redArg(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_bindAsync___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_7);
x_16 = l_Lake_BuildJob_bindAsync(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_wait_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_io_wait(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_wait_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_io_wait(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_add___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Job_add___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Job_add___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mix___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Job_mix___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_Job_mix___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildJob_mixList___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<collection>", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_3 = l_Lake_Job_mixList___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_4 = l_Lake_Job_mixList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_3 = l_Lake_Job_mixArray___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_4 = l_Lake_Job_mixArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildJob_mixArray___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_mixArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildJob_mixArray(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_apply_2(x_3, x_10, x_13);
x_16 = l_Lake_JobState_merge(x_11, x_14);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_apply_2(x_3, x_10, x_17);
x_20 = l_Lake_JobState_merge(x_11, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec_ref(x_2);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec_ref(x_4);
x_5 = x_22;
x_6 = x_23;
goto block_9;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec_ref(x_4);
x_5 = x_24;
x_6 = x_25;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lake_JobState_merge(x_5, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lake_BuildJob_zipWith___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_task_map(x_7, x_6, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
lean_dec(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_BuildJob_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_11);
x_13 = lean_task_bind(x_6, x_12, x_9, x_10);
x_14 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_15 = 0;
lean_ctor_set(x_3, 2, x_14);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_13);
lean_ctor_set_uint8(x_3, sizeof(void*)*3, x_15);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 1;
x_19 = lean_box(x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_BuildJob_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_19);
x_21 = lean_task_bind(x_16, x_20, x_17, x_18);
x_22 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lake_BuildJob_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_15, 0, x_7);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_5);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_task_bind(x_9, x_15, x_12, x_13);
x_17 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_18 = 0;
lean_ctor_set(x_6, 2, x_17);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_16);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_18);
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_BuildJob_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_23, 0, x_7);
lean_closure_set(x_23, 1, x_20);
lean_closure_set(x_23, 2, x_5);
lean_closure_set(x_23, 3, x_22);
x_24 = lean_task_bind(x_19, x_23, x_20, x_21);
x_25 = l_Lake_Job_zipResultWith___redArg___closed__0;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_zipWith___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
x_7 = l_Lake_BuildJob_zipWith___redArg___lam__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectList___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_3 = l_Lake_Job_collectList___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_4 = l_Lake_Job_collectList___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_3 = l_Lake_Job_collectArray___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_BuildJob_mixList___redArg___closed__0;
x_4 = l_Lake_Job_collectArray___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildJob_collectArray___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildJob_collectArray___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildJob_collectArray(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadStateOfJobStateJobM___closed__0 = _init_l_Lake_instMonadStateOfJobStateJobM___closed__0();
lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM___closed__0);
l_Lake_instMonadStateOfJobStateJobM___closed__1 = _init_l_Lake_instMonadStateOfJobStateJobM___closed__1();
lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM___closed__1);
l_Lake_instMonadStateOfJobStateJobM___closed__2 = _init_l_Lake_instMonadStateOfJobStateJobM___closed__2();
lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM___closed__2);
l_Lake_instMonadStateOfJobStateJobM___closed__3 = _init_l_Lake_instMonadStateOfJobStateJobM___closed__3();
lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM___closed__3);
l_Lake_instMonadStateOfJobStateJobM___closed__4 = _init_l_Lake_instMonadStateOfJobStateJobM___closed__4();
lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM___closed__4);
l_Lake_instMonadStateOfJobStateJobM = _init_l_Lake_instMonadStateOfJobStateJobM();
lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM);
l_Lake_instMonadStateOfLogJobM___closed__0 = _init_l_Lake_instMonadStateOfLogJobM___closed__0();
lean_mark_persistent(l_Lake_instMonadStateOfLogJobM___closed__0);
l_Lake_instMonadStateOfLogJobM = _init_l_Lake_instMonadStateOfLogJobM();
lean_mark_persistent(l_Lake_instMonadStateOfLogJobM);
l_Lake_instMonadLogJobM___closed__0 = _init_l_Lake_instMonadLogJobM___closed__0();
lean_mark_persistent(l_Lake_instMonadLogJobM___closed__0);
l_Lake_instMonadLogJobM = _init_l_Lake_instMonadLogJobM();
lean_mark_persistent(l_Lake_instMonadLogJobM);
l_Lake_instMonadErrorJobM = _init_l_Lake_instMonadErrorJobM();
lean_mark_persistent(l_Lake_instMonadErrorJobM);
l_Lake_instAlternativeJobM = _init_l_Lake_instAlternativeJobM();
lean_mark_persistent(l_Lake_instAlternativeJobM);
l_Lake_instMonadLiftLogIOJobM = _init_l_Lake_instMonadLiftLogIOJobM();
lean_mark_persistent(l_Lake_instMonadLiftLogIOJobM);
l_Lake_takeTrace___redArg___closed__0 = _init_l_Lake_takeTrace___redArg___closed__0();
lean_mark_persistent(l_Lake_takeTrace___redArg___closed__0);
l_Lake_takeTrace___redArg___closed__1 = _init_l_Lake_takeTrace___redArg___closed__1();
lean_mark_persistent(l_Lake_takeTrace___redArg___closed__1);
l_Lake_instMonadLiftSpawnMJobM___closed__0 = _init_l_Lake_instMonadLiftSpawnMJobM___closed__0();
lean_mark_persistent(l_Lake_instMonadLiftSpawnMJobM___closed__0);
l_Lake_instMonadLiftSpawnMJobM = _init_l_Lake_instMonadLiftSpawnMJobM();
lean_mark_persistent(l_Lake_instMonadLiftSpawnMJobM);
l_Lake_instMonadLiftJobMFetchM___closed__0 = _init_l_Lake_instMonadLiftJobMFetchM___closed__0();
lean_mark_persistent(l_Lake_instMonadLiftJobMFetchM___closed__0);
l_Lake_instMonadLiftJobMFetchM = _init_l_Lake_instMonadLiftJobMFetchM();
lean_mark_persistent(l_Lake_instMonadLiftJobMFetchM);
l_Lake_instMonadLiftFetchMJobM___closed__0 = _init_l_Lake_instMonadLiftFetchMJobM___closed__0();
lean_mark_persistent(l_Lake_instMonadLiftFetchMJobM___closed__0);
l_Lake_instMonadLiftFetchMJobM = _init_l_Lake_instMonadLiftFetchMJobM();
lean_mark_persistent(l_Lake_instMonadLiftFetchMJobM);
l_Lake_Job_async___redArg___lam__0___closed__0 = _init_l_Lake_Job_async___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lake_Job_async___redArg___lam__0___closed__0);
l_Lake_Job_async___redArg___lam__0___closed__1 = _init_l_Lake_Job_async___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lake_Job_async___redArg___lam__0___closed__1);
l_Lake_Job_async___redArg___closed__0 = _init_l_Lake_Job_async___redArg___closed__0();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__0);
l_Lake_Job_async___redArg___closed__1 = _init_l_Lake_Job_async___redArg___closed__1();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__1);
l_Lake_Job_async___redArg___closed__2 = _init_l_Lake_Job_async___redArg___closed__2();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__2);
l_Lake_Job_async___redArg___closed__3 = _init_l_Lake_Job_async___redArg___closed__3();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__3);
l_Lake_Job_async___redArg___closed__4 = _init_l_Lake_Job_async___redArg___closed__4();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__4);
l_Lake_Job_async___redArg___closed__5 = _init_l_Lake_Job_async___redArg___closed__5();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__5);
l_Lake_Job_async___redArg___closed__6 = _init_l_Lake_Job_async___redArg___closed__6();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__6);
l_Lake_Job_async___redArg___closed__7 = _init_l_Lake_Job_async___redArg___closed__7();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__7);
l_Lake_Job_async___redArg___closed__8 = _init_l_Lake_Job_async___redArg___closed__8();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__8);
l_Lake_Job_async___redArg___closed__9 = _init_l_Lake_Job_async___redArg___closed__9();
lean_mark_persistent(l_Lake_Job_async___redArg___closed__9);
l_Lake_Job_zipResultWith___redArg___closed__0 = _init_l_Lake_Job_zipResultWith___redArg___closed__0();
lean_mark_persistent(l_Lake_Job_zipResultWith___redArg___closed__0);
l_Lake_BuildJob_nil___closed__0 = _init_l_Lake_BuildJob_nil___closed__0();
lean_mark_persistent(l_Lake_BuildJob_nil___closed__0);
l_Lake_BuildJob_nil___closed__1 = _init_l_Lake_BuildJob_nil___closed__1();
lean_mark_persistent(l_Lake_BuildJob_nil___closed__1);
l_Lake_BuildJob_nil___closed__2 = _init_l_Lake_BuildJob_nil___closed__2();
lean_mark_persistent(l_Lake_BuildJob_nil___closed__2);
l_Lake_BuildJob_nil = _init_l_Lake_BuildJob_nil();
lean_mark_persistent(l_Lake_BuildJob_nil);
l_Lake_BuildJob_instPure = _init_l_Lake_BuildJob_instPure();
lean_mark_persistent(l_Lake_BuildJob_instPure);
l_Lake_BuildJob_instFunctor = _init_l_Lake_BuildJob_instFunctor();
lean_mark_persistent(l_Lake_BuildJob_instFunctor);
l_Lake_BuildJob_mixList___redArg___closed__0 = _init_l_Lake_BuildJob_mixList___redArg___closed__0();
lean_mark_persistent(l_Lake_BuildJob_mixList___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
