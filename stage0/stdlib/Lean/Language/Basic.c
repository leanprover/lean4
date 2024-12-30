// Lean compiler output
// Module: Lean.Language.Basic
// Imports: Init.System.Promise Lean.Parser.Types Lean.Util.Trace
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__5;
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lean_Language_reportMessages___spec__7(lean_object*, lean_object*);
lean_object* lean_io_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancel___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
static lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancel___rarg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_printMessageEndPos;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__33;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___rarg___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__26;
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___rarg(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__30;
static lean_object* l_Lean_Language_diagnosticsOfHeaderError___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lean_Language_reportMessages___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static uint64_t l_Lean_Language_instInhabitedSnapshot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_runAndReport___spec__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__40;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_Diagnostics_empty___closed__1;
static lean_object* l_Lean_Language_instInhabitedSnapshot___closed__3;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__23;
static lean_object* l_Lean_Language_reportMessages___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot(lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__9;
static lean_object* l_Lean_Language_withHeaderExceptions___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___lambda__1___boxed(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Message_toJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_reportMessages___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_Language_instInhabitedDynamicSnapshot___lambda__1(lean_object*);
static lean_object* l_Lean_Language_instInhabitedSnapshot___closed__4;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__20;
lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_Promise_new___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__36;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__34;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__19;
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__7;
static lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1;
static size_t l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__3;
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__6;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_instInhabitedSnapshotTree___closed__1;
static lean_object* l_Lean_Language_diagnosticsOfHeaderError___closed__1;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__8;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_pure(lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__21;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTree;
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_runAndReport___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Language_Basic___hyg_62_;
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986_;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__16;
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__5;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__13;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__17;
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__5;
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__2___boxed(lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__3;
static lean_object* l_Lean_Language_withHeaderExceptions___rarg___closed__3;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lean_Language_reportMessages___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
static lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lean_Language_reportMessages___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__22;
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
extern lean_object* l_Task_Priority_default;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___rarg(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
static lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__4;
extern lean_object* l_Lean_MessageLog_empty;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__29;
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__5;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__7;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___boxed(lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_getAll___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__11;
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_getAll___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_reportMessages___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lean_Language_reportMessages___spec__7___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__3;
static lean_object* l_Lean_Language_SnapshotTree_waitAll_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lean_Language_reportMessages___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__4;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__39;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_withHeaderExceptions___rarg___closed__1;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__37;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__41;
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__27;
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__25;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lean_Language_reportMessages___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___rarg(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__12;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__38;
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises(lean_object*, lean_object*);
static lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3___closed__1;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__31;
lean_object* l_List_iotaTR(lean_object*);
static lean_object* l_Lean_Language_instInhabitedSnapshot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___closed__1;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__9;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__18;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198_(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__28;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__24;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_runAndReport___spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__2;
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__32;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1___lambda__1(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__6;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__15;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__14;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lean_Language_reportMessages___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_getAll___spec__1(lean_object*, lean_object*);
static lean_object* l___auto____x40_Lean_Language_Basic___hyg_62____closed__35;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_runAndReport___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_pure___rarg(lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instTypeNameSnapshotLeaf;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__3() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; size_t x_4; lean_object* x_5; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__2;
x_2 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set_usize(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__4;
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__6;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MessageLog_empty;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_Diagnostics_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Snapshot_Diagnostics_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__2;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__3;
x_4 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__2;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__3;
x_4 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__2;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__3;
x_4 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__10;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__12;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__2;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__14;
x_4 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__15;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__2;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__14;
x_4 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__17;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__19;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__20;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__18;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__21;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__24;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__23;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__25;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toString", 8, 8);
return x_1;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__27;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__27;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__28;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__27;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(2);
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__29;
x_4 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__30;
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__26;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__31;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__16;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__32;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__13;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__33;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__11;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__34;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__35;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__9;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__36;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__37;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__7;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__38;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__39;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__5;
x_3 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__40;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___auto____x40_Lean_Language_Basic___hyg_62_() {
_start:
{
lean_object* x_1; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__41;
return x_1;
}
}
static uint64_t _init_l_Lean_Language_instInhabitedSnapshot___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__2() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_instInhabitedSnapshot___closed__1;
x_2 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__4;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_instInhabitedSnapshot___closed__3;
x_3 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__6;
x_4 = l_Lean_Language_instInhabitedSnapshot___closed__2;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshot___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_task_pure(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_instInhabitedSnapshotTask___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Task_Priority_default;
x_5 = lean_io_as_task(x_2, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
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
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_ofIO___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_pure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_task_pure(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_pure(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_pure___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancel___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_io_cancel(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancel___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancel___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotTask_cancel___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Task_Priority_default;
x_7 = lean_task_map(x_2, x_5, x_6, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_map___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Language_SnapshotTask_map___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bind___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Task_Priority_default;
x_8 = lean_task_bind(x_5, x_6, x_7, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bind___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bind___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Language_SnapshotTask_bind___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
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
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___rarg___lambda__1), 3, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = l_Task_Priority_default;
x_9 = lean_io_bind_task(x_6, x_7, x_8, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
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
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Language_SnapshotTask_bindIO___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_get___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_io_get_task_state(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_task_get_own(x_3);
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
x_11 = lean_task_get_own(x_3);
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
lean_dec(x_3);
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
else
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_get_x3f___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_6);
x_9 = lean_apply_1(x_2, x_6);
x_10 = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_6);
x_11 = lean_apply_2(x_4, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_12);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3___closed__1;
x_16 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
}
static lean_object* _init_l_Lean_Language_withAlwaysResolvedPromise___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_Promise_new___boxed), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Language_withAlwaysResolvedPromise___rarg___closed__1;
lean_inc(x_2);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_2);
lean_closure_set(x_9, 4, x_3);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromise___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = lean_array_uset(x_2, x_1, x_6);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_5, x_4, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = l_Lean_Language_withAlwaysResolvedPromise___rarg___closed__1;
lean_inc(x_2);
x_14 = lean_apply_2(x_2, lean_box(0), x_13);
x_15 = lean_box_usize(x_4);
x_16 = lean_box_usize(x_3);
x_17 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_11);
lean_closure_set(x_17, 2, x_1);
lean_closure_set(x_17, 3, x_2);
lean_closure_set(x_17, 4, x_16);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___closed__1;
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_10, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
x_16 = lean_array_uget(x_8, x_10);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_3);
lean_closure_set(x_18, 2, x_16);
lean_inc(x_2);
x_19 = lean_apply_2(x_2, lean_box(0), x_18);
lean_inc(x_6);
x_20 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_20, 0, x_6);
lean_inc(x_4);
x_21 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_box_usize(x_10);
x_23 = lean_box_usize(x_9);
x_24 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__2___boxed), 11, 10);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_6);
lean_closure_set(x_24, 7, x_7);
lean_closure_set(x_24, 8, x_8);
lean_closure_set(x_24, 9, x_23);
x_25 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___boxed), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_8);
x_11 = lean_apply_1(x_2, x_8);
x_12 = lean_box(0);
x_13 = lean_array_size(x_8);
x_14 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg(x_1, x_3, x_4, x_5, x_8, x_9, x_12, x_8, x_13, x_6, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_9);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_15, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_18);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3___closed__1;
x_22 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_21, x_19);
return x_22;
}
}
static lean_object* _init_l_Lean_Language_withAlwaysResolvedPromises___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_List_iotaTR(x_5);
x_9 = lean_array_mk(x_8);
x_10 = lean_array_size(x_9);
x_11 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg(x_1, x_2, x_10, x_11, x_9);
x_13 = l_Lean_Language_withAlwaysResolvedPromises___rarg___boxed__const__1;
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_3);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Language_withAlwaysResolvedPromises___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Language_withAlwaysResolvedPromises___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__2(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_13 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Lean_Language_withAlwaysResolvedPromises___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_instInhabitedSnapshot___closed__4;
x_2 = l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshotTree___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = l_Lean_Language_instInhabitedSnapshotTree___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Language", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SnapshotLeaf", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1;
x_3 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instTypeNameSnapshotLeaf() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986_;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_instToSnapshotTreeDynamicSnapshot(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_mk_thunk(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_DynamicSnapshot_ofTyped___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___rarg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_toTyped_x3f___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_DynamicSnapshot_toTyped_x3f___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_mk_thunk(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Language_instInhabitedDynamicSnapshot___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instInhabitedDynamicSnapshot", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1;
x_3 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instInhabitedDynamicSnapshot___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__2;
x_2 = 1;
x_3 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__6;
x_3 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__5;
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
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__8() {
_start:
{
uint64_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__7;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__4;
x_3 = l_Lean_Language_Snapshot_Diagnostics_empty;
x_4 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__8;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_instTypeNameSnapshotLeaf;
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__9;
x_3 = l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_DynamicSnapshot_ofTyped___at_Lean_Language_instInhabitedDynamicSnapshot___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Language_SnapshotTask_get___rarg(x_4);
x_6 = l_Lean_Language_SnapshotTree_forM___rarg(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_get_size(x_1);
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_5, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = l_Array_foldlMUnsafe_fold___rarg(x_2, x_6, x_1, x_18, x_19, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_3);
x_7 = lean_apply_1(x_3, x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___rarg___lambda__2___boxed), 4, 3);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_forM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_forM___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("printMessageEndPos", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("print end position of each message in addition to start position", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Language_instInhabitedSnapshot___closed__3;
x_3 = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1;
x_3 = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__2;
x_3 = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__4;
x_4 = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__5;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = l_Lean_PersistentArray_forMAux___at_Lean_Language_reportMessages___spec__3(x_1, x_8, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lean_Language_reportMessages___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__4(x_1, x_4, x_13, x_14, x_15, x_3);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_18, x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__5(x_1, x_17, x_26, x_27, x_28, x_3);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_3, x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_5 = x_10;
x_6 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lean_Language_reportMessages___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_5 = l_Lean_PersistentArray_forMAux___at_Lean_Language_reportMessages___spec__3(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_5);
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__6(x_1, x_9, x_16, x_17, x_18, x_7);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_22, x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__6(x_1, x_21, x_30, x_31, x_32, x_20);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lean_Language_reportMessages___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_PersistentArray_forM___at_Lean_Language_reportMessages___spec__2(x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lean_Language_reportMessages___spec__7___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_apply_1(x_2, x_6);
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
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at_Lean_Language_reportMessages___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Functor_mapRev___at_Lean_Language_reportMessages___spec__7___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_reportMessages___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_printMessageEndPos;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = l_Lean_Language_reportMessages___lambda__1___closed__1;
x_5 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_4);
x_6 = l_Lean_Message_toString(x_2, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_IO_print___at_IO_println___spec__1(x_7, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lean_Language_reportMessages___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_compress), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Message_toJson), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Language_reportMessages___lambda__2___closed__1;
x_5 = l_Functor_mapRev___at_Lean_Language_reportMessages___spec__7___rarg(x_3, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_6, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Language_reportMessages___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_reportMessages___lambda__2), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Language_reportMessages___lambda__1___boxed), 3, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_MessageLog_forM___at_Lean_Language_reportMessages___spec__1(x_1, x_5, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lean_Language_reportMessages___closed__1;
x_8 = l_Lean_MessageLog_forM___at_Lean_Language_reportMessages___spec__1(x_1, x_7, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__4(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__5(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lean_Language_reportMessages___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forMAux___at_Lean_Language_reportMessages___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Language_reportMessages___spec__6(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lean_Language_reportMessages___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentArray_forM___at_Lean_Language_reportMessages___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lean_Language_reportMessages___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageLog_forM___at_Lean_Language_reportMessages___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_reportMessages___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_reportMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Language_reportMessages(x_1, x_2, x_5, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_runAndReport___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = lean_array_uget(x_3, x_4);
x_10 = l_Lean_Language_SnapshotTask_get___rarg(x_9);
lean_inc(x_1);
x_11 = l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_runAndReport___spec__1(x_1, x_2, x_10, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_6 = x_12;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_17; 
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
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_runAndReport___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_1);
x_9 = l_Lean_Language_reportMessages(x_8, x_1, x_2, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_array_get_size(x_6);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_13, x_13);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_9);
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_runAndReport___spec__2(x_1, x_2, x_6, x_19, x_20, x_21, x_11);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_array_get_size(x_6);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_24, x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_34 = lean_box(0);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_runAndReport___spec__2(x_1, x_2, x_6, x_32, x_33, x_34, x_23);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_runAndReport___spec__1(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_runAndReport___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_runAndReport___spec__2(x_1, x_8, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_runAndReport___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_runAndReport___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Language_SnapshotTree_runAndReport(x_1, x_2, x_5, x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_getAll___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Language_SnapshotTask_get___rarg(x_7);
x_9 = l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_getAll___spec__1(x_8, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_getAll___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_push(x_2, x_4);
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
x_10 = lean_box(0);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
x_12 = lean_box(0);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_free_object(x_1);
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_getAll___spec__2(x_5, x_13, x_14, x_15, x_6);
lean_dec(x_5);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = lean_array_push(x_2, x_17);
x_20 = lean_array_get_size(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_20, x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_18);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_getAll___spec__2(x_18, x_28, x_29, x_30, x_19);
lean_dec(x_18);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1;
x_3 = l_Lean_Language_SnapshotTree_forM___at_Lean_Language_SnapshotTree_getAll___spec__1(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_getAll___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Language_SnapshotTree_getAll___spec__2(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTree_waitAll_go(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTree_waitAll_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Language_SnapshotTree_waitAll_go___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_waitAll_go___lambda__1___boxed), 3, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = l_Task_Priority_default;
x_10 = 0;
x_11 = lean_io_bind_task(x_7, x_8, x_9, x_10, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTree_waitAll_go___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_to_list(x_3);
x_5 = l_Lean_Language_SnapshotTree_waitAll_go(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_instMonadLiftProcessingMProcessingTIO___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_st_mk_ref(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_Lean_Language_diagnosticsOfHeaderError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_diagnosticsOfHeaderError___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<input>", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_5);
lean_dec(x_5);
x_7 = l_Lean_FileMap_toPosition(x_4, x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lean_MessageData_ofFormat(x_9);
x_11 = l_Lean_Language_diagnosticsOfHeaderError___closed__2;
x_12 = l_Lean_Language_diagnosticsOfHeaderError___closed__1;
x_13 = 0;
x_14 = 2;
x_15 = l_Lean_Language_instInhabitedSnapshot___closed__3;
x_16 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_14);
x_17 = l_Lean_MessageLog_empty;
x_18 = l_Lean_MessageLog_add(x_16, x_17);
x_19 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_18, x_3);
return x_19;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withHeaderExceptions", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___auto____x40_Lean_Language_Basic___hyg_62____closed__1;
x_2 = l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1;
x_3 = l_Lean_Language_withHeaderExceptions___rarg___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___rarg___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_withHeaderExceptions___rarg___closed__2;
x_2 = 1;
x_3 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_io_error_to_string(x_10);
x_13 = l_Lean_Language_diagnosticsOfHeaderError(x_12, x_3, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
x_17 = l_Lean_Language_withHeaderExceptions___rarg___closed__3;
x_18 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__8;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*4, x_19);
x_21 = lean_apply_1(x_1, x_20);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = l_Lean_Language_withHeaderExceptions___rarg___closed__3;
x_26 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__8;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
x_29 = lean_apply_1(x_1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_withHeaderExceptions___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_st_ref_get(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_1, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_st_ref_set(x_2, x_11, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_9);
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
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_5);
if (x_25 == 0)
{
return x_5;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_st_mk_ref(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg___boxed), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
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
x_10 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg___boxed), 4, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_mkIncrementalProcessor___elambda__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_System_Promise(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__1);
l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__2 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__2();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__2);
l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__3 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__3();
l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__4 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__4();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__4);
l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__5 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__5();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__5);
l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__6 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__6();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics___closed__6);
l_Lean_Language_Snapshot_instInhabitedDiagnostics = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics);
l_Lean_Language_Snapshot_Diagnostics_empty___closed__1 = _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__1();
lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty___closed__1);
l_Lean_Language_Snapshot_Diagnostics_empty = _init_l_Lean_Language_Snapshot_Diagnostics_empty();
lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__1 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__1();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__1);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__2 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__2();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__2);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__3 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__3();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__3);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__4 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__4();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__4);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__5 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__5();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__5);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__6 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__6();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__6);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__7 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__7();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__7);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__8 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__8();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__8);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__9 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__9();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__9);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__10 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__10();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__10);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__11 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__11();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__11);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__12 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__12();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__12);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__13 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__13();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__13);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__14 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__14();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__14);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__15 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__15();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__15);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__16 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__16();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__16);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__17 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__17();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__17);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__18 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__18();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__18);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__19 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__19();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__19);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__20 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__20();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__20);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__21 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__21();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__21);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__22 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__22();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__22);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__23 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__23();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__23);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__24 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__24();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__24);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__25 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__25();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__25);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__26 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__26();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__26);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__27 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__27();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__27);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__28 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__28();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__28);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__29 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__29();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__29);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__30 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__30();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__30);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__31 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__31();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__31);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__32 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__32();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__32);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__33 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__33();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__33);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__34 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__34();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__34);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__35 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__35();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__35);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__36 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__36();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__36);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__37 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__37();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__37);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__38 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__38();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__38);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__39 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__39();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__39);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__40 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__40();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__40);
l___auto____x40_Lean_Language_Basic___hyg_62____closed__41 = _init_l___auto____x40_Lean_Language_Basic___hyg_62____closed__41();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62____closed__41);
l___auto____x40_Lean_Language_Basic___hyg_62_ = _init_l___auto____x40_Lean_Language_Basic___hyg_62_();
lean_mark_persistent(l___auto____x40_Lean_Language_Basic___hyg_62_);
l_Lean_Language_instInhabitedSnapshot___closed__1 = _init_l_Lean_Language_instInhabitedSnapshot___closed__1();
l_Lean_Language_instInhabitedSnapshot___closed__2 = _init_l_Lean_Language_instInhabitedSnapshot___closed__2();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot___closed__2);
l_Lean_Language_instInhabitedSnapshot___closed__3 = _init_l_Lean_Language_instInhabitedSnapshot___closed__3();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot___closed__3);
l_Lean_Language_instInhabitedSnapshot___closed__4 = _init_l_Lean_Language_instInhabitedSnapshot___closed__4();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot___closed__4);
l_Lean_Language_instInhabitedSnapshot = _init_l_Lean_Language_instInhabitedSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot);
l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3___closed__1 = _init_l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Language_withAlwaysResolvedPromise___rarg___lambda__3___closed__1);
l_Lean_Language_withAlwaysResolvedPromise___rarg___closed__1 = _init_l_Lean_Language_withAlwaysResolvedPromise___rarg___closed__1();
lean_mark_persistent(l_Lean_Language_withAlwaysResolvedPromise___rarg___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Language_withAlwaysResolvedPromises___spec__2___rarg___lambda__1___closed__1);
l_Lean_Language_withAlwaysResolvedPromises___rarg___boxed__const__1 = _init_l_Lean_Language_withAlwaysResolvedPromises___rarg___boxed__const__1();
lean_mark_persistent(l_Lean_Language_withAlwaysResolvedPromises___rarg___boxed__const__1);
l_Lean_Language_instInhabitedSnapshotTree___closed__1 = _init_l_Lean_Language_instInhabitedSnapshotTree___closed__1();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree___closed__1);
l_Lean_Language_instInhabitedSnapshotTree = _init_l_Lean_Language_instInhabitedSnapshotTree();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree);
l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1 = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__1);
l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__2 = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__2();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__2);
l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__3 = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__3();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986____closed__3);
l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986_ = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986_();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic___hyg_986_);
l_Lean_Language_instTypeNameSnapshotLeaf = _init_l_Lean_Language_instTypeNameSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instTypeNameSnapshotLeaf);
l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1 = _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___closed__1);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__1 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__1();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__1);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__2 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__2();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__2);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__3 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__3);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__4 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__4);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__5 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__5();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__5);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__6 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__6();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__6);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__7 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__7();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__7);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__8 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__8();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__8);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__9 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__9();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__9);
l_Lean_Language_instInhabitedDynamicSnapshot = _init_l_Lean_Language_instInhabitedDynamicSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot);
l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__1 = _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__1();
lean_mark_persistent(l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__1);
l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__2 = _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__2();
lean_mark_persistent(l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__2);
l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__3 = _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__3();
lean_mark_persistent(l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__3);
l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__4 = _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__4();
lean_mark_persistent(l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__4);
l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__5 = _init_l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__5();
lean_mark_persistent(l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198____closed__5);
if (builtin) {res = l_Lean_Language_initFn____x40_Lean_Language_Basic___hyg_1198_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_printMessageEndPos = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_printMessageEndPos);
lean_dec_ref(res);
}l_Lean_Language_reportMessages___lambda__1___closed__1 = _init_l_Lean_Language_reportMessages___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Language_reportMessages___lambda__1___closed__1);
l_Lean_Language_reportMessages___lambda__2___closed__1 = _init_l_Lean_Language_reportMessages___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Language_reportMessages___lambda__2___closed__1);
l_Lean_Language_reportMessages___closed__1 = _init_l_Lean_Language_reportMessages___closed__1();
lean_mark_persistent(l_Lean_Language_reportMessages___closed__1);
l_Lean_Language_SnapshotTree_waitAll_go___closed__1 = _init_l_Lean_Language_SnapshotTree_waitAll_go___closed__1();
lean_mark_persistent(l_Lean_Language_SnapshotTree_waitAll_go___closed__1);
l_Lean_Language_diagnosticsOfHeaderError___closed__1 = _init_l_Lean_Language_diagnosticsOfHeaderError___closed__1();
lean_mark_persistent(l_Lean_Language_diagnosticsOfHeaderError___closed__1);
l_Lean_Language_diagnosticsOfHeaderError___closed__2 = _init_l_Lean_Language_diagnosticsOfHeaderError___closed__2();
lean_mark_persistent(l_Lean_Language_diagnosticsOfHeaderError___closed__2);
l_Lean_Language_withHeaderExceptions___rarg___closed__1 = _init_l_Lean_Language_withHeaderExceptions___rarg___closed__1();
lean_mark_persistent(l_Lean_Language_withHeaderExceptions___rarg___closed__1);
l_Lean_Language_withHeaderExceptions___rarg___closed__2 = _init_l_Lean_Language_withHeaderExceptions___rarg___closed__2();
lean_mark_persistent(l_Lean_Language_withHeaderExceptions___rarg___closed__2);
l_Lean_Language_withHeaderExceptions___rarg___closed__3 = _init_l_Lean_Language_withHeaderExceptions___rarg___closed__3();
lean_mark_persistent(l_Lean_Language_withHeaderExceptions___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
