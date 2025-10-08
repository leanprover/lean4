// Lean compiler output
// Module: Lean.Language.Basic
// Imports: public import Init.System.Promise public import Lean.Parser.Types public import Lean.Util.Trace
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
static lean_object* l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
static lean_object* l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__5;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_printMessageEndPos;
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0;
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__36;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedDynamicSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__6;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_ToSnapshotTree_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_instInhabitedSnapshotTree_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__5;
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_ctorIdx___boxed(lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__26;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__0;
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
static lean_object* l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__2;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__2;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__33;
static lean_object* l_Lean_Language_Snapshot_Diagnostics_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__22;
static lean_object* l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__21;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__30;
LEAN_EXPORT lean_object* l_Lean_Language_ProcessingContext_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot;
static lean_object* l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__13;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SyntaxGuarded_ctorIdx(lean_object*, lean_object*);
lean_object* l_Lean_Message_toJson(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_ToSnapshotTree_ctorIdx(lean_object*, lean_object*);
static lean_object* l_Lean_Language_instInhabitedSnapshotTree_default___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__25;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(lean_object*);
lean_object* lean_get_stdout(lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__32;
static lean_object* l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__10;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__11;
lean_object* lean_task_pure(lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__7;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__14;
static lean_object* l_Lean_Language_diagnosticsOfHeaderError___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_ProcessingContext_ctorIdx(lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__8;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__23;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object*, lean_object*);
static lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTree;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__18;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__19;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTree_default;
LEAN_EXPORT lean_object* l_Lean_Language_maxErrors;
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotBundle_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_ctorIdx(lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__4;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object*);
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__6;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default(lean_object*, lean_object*);
lean_object* l_IO_CancelToken_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_instInhabitedReportingRange;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__17;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__16;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__34;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_withHeaderExceptions___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(lean_object*);
extern lean_object* l_Lean_instInhabitedMessageLog_default;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__39;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instImpl____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__15;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__27;
static lean_object* l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
static lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshot_default;
static lean_object* l_Lean_Language_instInhabitedSnapshot_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshot;
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_empty;
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotLeaf;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Language_withHeaderExceptions___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_instImpl___closed__2____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ctorIdx(lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__28;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__0;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__4;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0;
static lean_object* l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__8;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__3;
static lean_object* l_Lean_Language_SnapshotTree_getAll___closed__0;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__31;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__35;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotBundle_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotLeaf_ctorIdx(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Language_diagnosticsOfHeaderError___closed__0;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__29;
static lean_object* l_Lean_Language_withHeaderExceptions___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__7;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object*);
lean_object* lean_io_get_task_state(lean_object*, lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instTypeNameSnapshotTree;
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__37;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_ctorIdx(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__2;
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ctorIdx(lean_object*, lean_object*);
static lean_object* l_Lean_Language_instInhabitedSnapshot_default___closed__2;
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object*);
static lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0;
static lean_object* l_Lean_Language_instInhabitedDynamicSnapshot___closed__9;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotLeaf_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__40;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotLeaf_default;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ctorIdx(lean_object*);
static lean_object* l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__24;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf;
static lean_object* l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0;
lean_object* l_Lean_mkAtom(lean_object*);
extern lean_object* l_Lean_instInhabitedTraceState_default;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_desc___autoParam;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__20;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__41;
static lean_object* l_Lean_Language_Snapshot_desc___autoParam___closed__38;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SyntaxGuarded_ctorIdx___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Language_Snapshot_Diagnostics_empty___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Language_instInhabitedSnapshot_default___closed__1;
static lean_object* l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_instTypeNameSnapshotLeaf;
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Snapshot_Diagnostics_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedMessageLog_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MessageLog_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Snapshot_Diagnostics_empty___closed__0;
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
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__3;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__2;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__1;
x_4 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__6;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__2;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__1;
x_4 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exact", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__10;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__2;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__1;
x_4 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__10;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__12;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__15;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__14;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__1;
x_4 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__17;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__14;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__1;
x_4 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decl_name%", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__19;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__20;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__21;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__18;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__22;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__24;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__25;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__23;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toString", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__27;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__28;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__27;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__27;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__30;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__29;
x_4 = lean_box(2);
x_5 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__31;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__26;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__32;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__16;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__33;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__34;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__11;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__35;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__36;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__9;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__37;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__38;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__7;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__39;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__40;
x_2 = l_Lean_Language_Snapshot_desc___autoParam___closed__4;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_Snapshot_desc___autoParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_Snapshot_desc___autoParam___closed__41;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_Snapshot_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedTraceState_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot_default___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lean_Language_instInhabitedSnapshot_default___closed__1;
x_3 = lean_box(0);
x_4 = l_Lean_Language_Snapshot_instInhabitedDiagnostics_default;
x_5 = l_Lean_Language_instInhabitedSnapshot_default___closed__0;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshot_default___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshot_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_SnapshotTask_ReportingRange_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_inherit_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_some_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_skip_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_ReportingRange_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(lean_object* x_1) {
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
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0;
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = 1;
x_5 = l_Lean_Syntax_getRange_x3f(x_3, x_4);
x_6 = l_Lean_Language_SnapshotTask_ReportingRange_ofOptionInheriting(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_defaultReportingRange___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_SnapshotTask_defaultReportingRange(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotTask_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_task_pure(x_1);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask_default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instInhabitedSnapshotTask(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_instInhabitedSnapshotTask_default___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_io_as_task(x_4, x_6, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_2);
lean_ctor_set(x_10, 3, x_9);
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
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 2, x_2);
lean_ctor_set(x_13, 3, x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_ofIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Language_SnapshotTask_ofIO___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(2);
x_4 = lean_box(0);
x_5 = lean_task_pure(x_2);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_finished(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTask_finished___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 0);
lean_dec(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_task_map(x_2, x_7, x_10, x_5);
lean_ctor_set(x_1, 3, x_11);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_task_map(x_2, x_13, x_14, x_5);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Language_SnapshotTask_map___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Language_SnapshotTask_map___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Language_SnapshotTask_map(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 3);
lean_inc_ref(x_7);
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
x_10 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0), 3, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_io_bind_task(x_9, x_13, x_14, x_6, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set(x_1, 2, x_5);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_3);
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
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set(x_1, 2, x_5);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_bindIO___redArg___lam__0), 3, 1);
lean_closure_set(x_22, 0, x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_io_bind_task(x_21, x_22, x_23, x_6, x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 2, x_5);
lean_ctor_set(x_28, 3, x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Language_SnapshotTask_bindIO___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
x_9 = l_Lean_Language_SnapshotTask_bindIO___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_bindIO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_8);
x_11 = l_Lean_Language_SnapshotTask_bindIO(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_task_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotTask_get___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_io_get_task_state(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 2)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_task_get_own(x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_task_get_own(x_3);
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
lean_dec_ref(x_3);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_4, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_get_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_SnapshotTask_get_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SyntaxGuarded_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SyntaxGuarded_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SyntaxGuarded_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotBundle_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotBundle_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_SnapshotBundle_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_SnapshotTree_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Language_instInhabitedSnapshotTree_default___closed__0;
x_2 = l_Lean_Language_instInhabitedSnapshot_default;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshotTree_default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotTree() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshotTree_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Language", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SnapshotTree", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instImpl___closed__2____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
x_2 = l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl___closed__2____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instTypeNameSnapshotTree() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_ToSnapshotTree_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_ToSnapshotTree_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_ToSnapshotTree_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeSnapshotTree() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_Lean_Language_instInhabitedSnapshotTree_default;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_instToSnapshotTreeOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_cancelRec___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_apply_1(x_1, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_8);
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_6);
x_15 = 0;
x_16 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_8, x_15, x_16, x_12);
x_18 = lean_apply_1(x_17, x_5);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_19);
x_22 = lean_box(0);
x_23 = lean_nat_dec_lt(x_20, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_21, x_21);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_21);
lean_dec_ref(x_19);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_3, x_19, x_27, x_28, x_22);
x_30 = lean_apply_1(x_29, x_5);
return x_30;
}
}
}
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotTree___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0;
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__0), 4, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTask_cancelRec___redArg___lam__1), 5, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_8);
if (lean_obj_tag(x_5) == 0)
{
x_10 = x_3;
goto block_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec_ref(x_5);
x_16 = l_IO_CancelToken_set(x_15, x_3);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_10 = x_17;
goto block_14;
}
block_14:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = 1;
x_13 = l_BaseIO_chainTask___redArg(x_6, x_9, x_11, x_12, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_cancelRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTask_cancelRec___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotLeaf_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotLeaf_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_SnapshotLeaf_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshot_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedSnapshotLeaf() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedSnapshot_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SnapshotLeaf", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_;
x_2 = l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instTypeNameSnapshotLeaf() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instImpl____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_;
return x_1;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_DynamicSnapshot_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instToSnapshotTreeDynamicSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_instToSnapshotTreeDynamicSnapshot___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_4 = lean_alloc_closure((void*)(l_Lean_Language_DynamicSnapshot_ofTyped___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_mk_thunk(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_ofTyped(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Language_DynamicSnapshot_toTyped_x3f___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_DynamicSnapshot_toTyped_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_DynamicSnapshot_toTyped_x3f(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0), 1, 0);
return x_1;
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
x_1 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__1;
x_2 = l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__2;
x_3 = l_Lean_Name_toString(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__4;
x_4 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__7() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__6;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__7;
x_3 = lean_box(0);
x_4 = l_Lean_Language_Snapshot_Diagnostics_empty;
x_5 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__3;
x_6 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__8;
x_2 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__0;
x_3 = l_Lean_Language_instImpl____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_;
x_4 = l_Lean_Language_DynamicSnapshot_ofTyped___redArg(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_instInhabitedDynamicSnapshot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__9;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Language_SnapshotTask_get___redArg(x_4);
x_6 = l_Lean_Language_SnapshotTree_forM___redArg(x_1, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_1);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_apply_2(x_13, lean_box(0), x_8);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
lean_dec_ref(x_2);
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_15, x_16, x_8);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_2);
lean_inc(x_3);
lean_inc_ref(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__0), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_forM___redArg___lam__1), 5, 4);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_8);
x_10 = lean_apply_1(x_3, x_6);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_SnapshotTree_forM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Language_SnapshotTask_get___redArg(x_4);
x_6 = l_Lean_Language_SnapshotTree_foldM___redArg(x_1, x_5, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_apply_2(x_9, lean_box(0), x_5);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
x_13 = lean_apply_2(x_12, lean_box(0), x_5);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
lean_dec_ref(x_2);
x_14 = 0;
x_15 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_1, x_14, x_15, x_5);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
lean_inc(x_3);
lean_inc_ref(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__0), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldM___redArg___lam__1), 5, 4);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_2(x_3, x_4, x_7);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Language_SnapshotTree_foldM___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("printMessageEndPos", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("print end position of each message in addition to start position", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
x_2 = l_Lean_Language_instInhabitedSnapshot_default___closed__0;
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
x_2 = l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
x_3 = l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
x_4 = l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4__spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxErrors", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum number of errors to report (0 for no limit)", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
x_2 = l_Lean_Language_instInhabitedSnapshot_default___closed__0;
x_3 = lean_unsigned_to_nat(100u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
x_2 = l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
x_3 = l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
x_4 = l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4__spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_print___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stdout(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__4(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_6, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_5, x_6);
x_12 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_11, x_8, x_9);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_6, x_15);
x_6 = x_16;
x_8 = x_13;
x_9 = x_14;
goto _start;
}
else
{
return x_12;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum number of errors (", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("; from option `maxErrors`) reached, exiting", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_maxErrors;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_51; 
x_51 = lean_usize_dec_eq(x_6, x_7);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_104; uint8_t x_112; 
x_52 = lean_array_uget(x_5, x_6);
x_112 = lean_ctor_get_uint8(x_52, sizeof(void*)*5 + 1);
if (x_112 == 2)
{
lean_object* x_113; 
x_113 = lean_unsigned_to_nat(1u);
x_104 = x_113;
goto block_111;
}
else
{
lean_object* x_114; 
x_114 = lean_unsigned_to_nat(0u);
x_104 = x_114;
goto block_111;
}
block_103:
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_53);
x_56 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_57);
x_58 = lean_ctor_get(x_52, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_52, sizeof(void*)*5);
x_60 = lean_ctor_get_uint8(x_52, sizeof(void*)*5 + 2);
x_61 = lean_ctor_get(x_52, 3);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_52, 4);
lean_inc(x_62);
x_63 = l_Lean_MessageData_kind(x_62);
x_64 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___Lean_NameMap_find_x3f_spec__0___redArg(x_4, x_63);
lean_dec(x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_56);
x_65 = lean_ctor_get_uint8(x_52, sizeof(void*)*5 + 2);
x_27 = x_54;
x_28 = x_55;
x_29 = x_52;
x_30 = x_65;
goto block_50;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_52);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_52, 4);
lean_dec(x_67);
x_68 = lean_ctor_get(x_52, 3);
lean_dec(x_68);
x_69 = lean_ctor_get(x_52, 2);
lean_dec(x_69);
x_70 = lean_ctor_get(x_52, 1);
lean_dec(x_70);
x_71 = lean_ctor_get(x_52, 0);
lean_dec(x_71);
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec_ref(x_64);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
lean_ctor_set_uint8(x_52, sizeof(void*)*5 + 1, x_73);
x_27 = x_54;
x_28 = x_55;
x_29 = x_52;
x_30 = x_60;
goto block_50;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_52);
x_74 = lean_ctor_get(x_64, 0);
lean_inc(x_74);
lean_dec_ref(x_64);
x_75 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set(x_75, 1, x_57);
lean_ctor_set(x_75, 2, x_58);
lean_ctor_set(x_75, 3, x_61);
lean_ctor_set(x_75, 4, x_62);
lean_ctor_set_uint8(x_75, sizeof(void*)*5, x_59);
x_76 = lean_unbox(x_74);
lean_dec(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*5 + 1, x_76);
lean_ctor_set_uint8(x_75, sizeof(void*)*5 + 2, x_60);
x_27 = x_54;
x_28 = x_55;
x_29 = x_75;
x_30 = x_60;
goto block_50;
}
}
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_52);
if (x_77 == 0)
{
uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_78 = lean_ctor_get_uint8(x_52, sizeof(void*)*5 + 2);
x_79 = lean_ctor_get(x_52, 4);
lean_dec(x_79);
x_80 = 2;
x_81 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__0;
x_82 = l_Nat_reprFast(x_53);
x_83 = lean_string_append(x_81, x_82);
lean_dec_ref(x_82);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__1;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lean_MessageData_ofFormat(x_86);
lean_ctor_set(x_52, 4, x_87);
lean_ctor_set_uint8(x_52, sizeof(void*)*5 + 1, x_80);
x_27 = x_54;
x_28 = x_55;
x_29 = x_52;
x_30 = x_78;
goto block_50;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_88 = lean_ctor_get(x_52, 0);
x_89 = lean_ctor_get(x_52, 1);
x_90 = lean_ctor_get(x_52, 2);
x_91 = lean_ctor_get_uint8(x_52, sizeof(void*)*5);
x_92 = lean_ctor_get_uint8(x_52, sizeof(void*)*5 + 2);
x_93 = lean_ctor_get(x_52, 3);
lean_inc(x_93);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_52);
x_94 = 2;
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__0;
x_96 = l_Nat_reprFast(x_53);
x_97 = lean_string_append(x_95, x_96);
lean_dec_ref(x_96);
x_98 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__1;
x_99 = lean_string_append(x_97, x_98);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Lean_MessageData_ofFormat(x_100);
x_102 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_102, 0, x_88);
lean_ctor_set(x_102, 1, x_89);
lean_ctor_set(x_102, 2, x_90);
lean_ctor_set(x_102, 3, x_93);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*5, x_91);
lean_ctor_set_uint8(x_102, sizeof(void*)*5 + 1, x_94);
lean_ctor_set_uint8(x_102, sizeof(void*)*5 + 2, x_92);
x_27 = x_54;
x_28 = x_55;
x_29 = x_102;
x_30 = x_92;
goto block_50;
}
}
}
block_111:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_nat_add(x_8, x_104);
lean_dec(x_8);
x_106 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__2;
x_107 = l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(x_1, x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_eq(x_107, x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_nat_dec_lt(x_107, x_105);
if (x_110 == 0)
{
x_53 = x_107;
x_54 = x_105;
x_55 = x_51;
goto block_103;
}
else
{
x_53 = x_107;
x_54 = x_105;
x_55 = x_110;
goto block_103;
}
}
else
{
x_53 = x_107;
x_54 = x_105;
x_55 = x_51;
goto block_103;
}
}
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_8);
lean_ctor_set(x_115, 1, x_9);
return x_115;
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_6, x_12);
x_6 = x_13;
x_8 = x_10;
x_9 = x_11;
goto _start;
}
block_26:
{
if (x_17 == 0)
{
x_10 = x_16;
x_11 = x_18;
goto block_15;
}
else
{
uint8_t x_19; lean_object* x_20; 
x_19 = 1;
x_20 = lean_io_exit(x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_10 = x_16;
x_11 = x_21;
goto block_15;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
block_50:
{
if (x_30 == 0)
{
if (x_2 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Message_toString(x_29, x_3, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_IO_print___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__2(x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec_ref(x_34);
x_16 = x_27;
x_17 = x_28;
x_18 = x_35;
goto block_26;
}
else
{
uint8_t x_36; 
lean_dec(x_27);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Lean_Message_toJson(x_29, x_9);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = l_Lean_Json_compress(x_41);
x_44 = l_IO_println___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__3(x_43, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_16 = x_27;
x_17 = x_28;
x_18 = x_45;
goto block_26;
}
else
{
uint8_t x_46; 
lean_dec(x_27);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_dec_ref(x_29);
x_16 = x_27;
x_17 = x_28;
x_18 = x_9;
goto block_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_8, x_15, x_16, x_6, x_7);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_20, x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(x_1, x_2, x_3, x_4, x_18, x_25, x_26, x_6, x_7);
return x_27;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0;
x_12 = lean_usize_shift_right(x_6, x_7);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_array_get_borrowed(x_11, x_10, x_13);
x_15 = 1;
x_16 = lean_usize_shift_left(x_15, x_7);
x_17 = lean_usize_sub(x_16, x_15);
x_18 = lean_usize_land(x_6, x_17);
x_19 = 5;
x_20 = lean_usize_sub(x_7, x_19);
x_21 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(x_1, x_2, x_3, x_4, x_14, x_18, x_20, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_13, x_24);
lean_dec(x_13);
x_26 = lean_array_get_size(x_10);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
return x_21;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_26, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
return x_21;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_dec_ref(x_21);
x_29 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_10, x_29, x_30, x_22, x_23);
return x_31;
}
}
}
else
{
lean_dec(x_13);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_usize_to_nat(x_6);
x_34 = lean_array_get_size(x_32);
x_35 = lean_nat_dec_lt(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_34);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_9);
return x_38;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_40 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_41 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(x_1, x_2, x_3, x_4, x_32, x_39, x_40, x_8, x_9);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get_usize(x_5, 4);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_nat_dec_le(x_14, x_7);
if (x_15 == 0)
{
size_t x_16; lean_object* x_17; 
x_16 = lean_usize_of_nat(x_7);
x_17 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(x_1, x_2, x_3, x_4, x_11, x_16, x_13, x_6, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_array_get_size(x_12);
x_21 = lean_nat_dec_lt(x_9, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_20, x_20);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec_ref(x_17);
x_23 = 0;
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(x_1, x_2, x_3, x_4, x_12, x_23, x_24, x_18, x_19);
return x_25;
}
}
}
else
{
return x_17;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_nat_sub(x_7, x_14);
x_27 = lean_array_get_size(x_12);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_27, x_27);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_33 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(x_1, x_2, x_3, x_4, x_12, x_32, x_33, x_6, x_8);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_5, 1);
x_37 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4(x_1, x_2, x_3, x_4, x_35, x_6, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_array_get_size(x_36);
x_41 = lean_nat_dec_lt(x_9, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
return x_37;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
return x_37;
}
else
{
size_t x_43; size_t x_44; lean_object* x_45; 
lean_dec_ref(x_37);
x_43 = 0;
x_44 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_45 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(x_1, x_2, x_3, x_4, x_36, x_43, x_44, x_38, x_39);
return x_45;
}
}
}
else
{
return x_37;
}
}
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Language_printMessageEndPos;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___closed__0;
x_9 = l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(x_2, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(x_2, x_3, x_9, x_4, x_7, x_5, x_10, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__4(x_1, x_10, x_11, x_4, x_5, x_12, x_13, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5(x_1, x_10, x_11, x_4, x_5, x_12, x_13, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
x_9 = lean_unbox(x_3);
x_10 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4(x_1, x_10, x_11, x_4, x_5, x_12, x_13, x_8, x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_4, x_5);
x_11 = l_Lean_Language_SnapshotTask_get___redArg(x_10);
x_12 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(x_1, x_2, x_3, x_11, x_7, x_8);
lean_dec_ref(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_7 = x_13;
x_8 = x_14;
goto _start;
}
else
{
return x_12;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_8, 0);
x_11 = l___private_Lean_Language_Basic_0__Lean_Language_reportMessages(x_10, x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_9);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_15, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec_ref(x_11);
x_18 = 0;
x_19 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_20 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(x_1, x_2, x_3, x_9, x_18, x_19, x_12, x_13);
return x_20;
}
}
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(x_2, x_3, x_4, x_1, x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
x_11 = lean_box(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_nat_dec_lt(x_6, x_12);
lean_dec(x_12);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0_spec__0(x_1, x_9, x_3, x_4, x_10, x_11, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_runAndReport_spec__0(x_1, x_7, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_runAndReport___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lean_Language_SnapshotTree_runAndReport(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Language_SnapshotTask_get___redArg(x_6);
x_8 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(x_7, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_array_push(x_2, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_4);
return x_5;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_7, x_7);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_4);
return x_5;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(x_4, x_10, x_11, x_5);
lean_dec_ref(x_4);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Language_SnapshotTree_getAll___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Language_SnapshotTree_getAll___closed__0;
x_3 = l_Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Language_SnapshotTree_foldM___at___Lean_Language_SnapshotTree_getAll_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_to_list(x_4);
x_6 = l_List_appendTR___redArg(x_5, x_1);
x_7 = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(x_6, x_3);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_task_pure(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0;
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
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___lam__0), 3, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 1;
x_11 = lean_io_bind_task(x_7, x_8, x_9, x_10, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_waitAll(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_array_to_list(x_3);
x_5 = l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_ProcessingContext_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_ProcessingContext_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Language_ProcessingContext_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_apply_2(x_2, x_3, x_4);
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
}
static lean_object* _init_l_Lean_Language_instMonadLiftProcessingMProcessingTIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Language_instMonadLiftProcessingMProcessingTIO___lam__0), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_st_mk_ref(x_3, x_2);
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
}
static lean_object* _init_l_Lean_Language_diagnosticsOfHeaderError___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<input>", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_diagnosticsOfHeaderError___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_diagnosticsOfHeaderError(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Lean_Language_diagnosticsOfHeaderError___closed__0;
x_7 = l_Lean_Language_diagnosticsOfHeaderError___closed__1;
x_8 = lean_string_utf8_byte_size(x_5);
x_9 = l_Lean_FileMap_toPosition(x_4, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 0;
x_12 = 2;
x_13 = l_Lean_Language_instInhabitedSnapshot_default___closed__0;
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 2, x_11);
x_17 = l_Lean_Language_Snapshot_Diagnostics_empty___closed__0;
x_18 = l_Lean_MessageLog_add(x_16, x_17);
x_19 = l_Lean_Language_Snapshot_Diagnostics_ofMessageLog(x_18, x_3);
return x_19;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("withHeaderExceptions", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Language_withHeaderExceptions___redArg___closed__0;
x_2 = l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_;
x_3 = l_Lean_Language_Snapshot_desc___autoParam___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lean_Language_withHeaderExceptions___redArg___closed__1;
x_3 = l_Lean_Name_toString(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc_ref(x_3);
x_5 = lean_apply_2(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec_ref(x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec_ref(x_5);
x_12 = lean_io_error_to_string(x_10);
x_13 = l_Lean_Language_diagnosticsOfHeaderError(x_12, x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Language_withHeaderExceptions___redArg___closed__2;
x_17 = lean_box(0);
x_18 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__7;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
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
x_24 = l_Lean_Language_withHeaderExceptions___redArg___closed__2;
x_25 = lean_box(0);
x_26 = l_Lean_Language_instInhabitedDynamicSnapshot___closed__7;
x_27 = 0;
x_28 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
x_29 = lean_apply_1(x_1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_withHeaderExceptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Language_withHeaderExceptions___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_st_ref_set(x_1, x_11, x_10);
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
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_box(0);
x_4 = lean_st_mk_ref(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
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
x_10 = lean_alloc_closure((void*)(l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Language_mkIncrementalProcessor___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_mkIncrementalProcessor___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Language_mkIncrementalProcessor___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
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
l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__0);
l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__1 = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__1();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics_default___closed__1);
l_Lean_Language_Snapshot_instInhabitedDiagnostics_default = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics_default();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics_default);
l_Lean_Language_Snapshot_instInhabitedDiagnostics = _init_l_Lean_Language_Snapshot_instInhabitedDiagnostics();
lean_mark_persistent(l_Lean_Language_Snapshot_instInhabitedDiagnostics);
l_Lean_Language_Snapshot_Diagnostics_empty___closed__0 = _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__0();
lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty___closed__0);
l_Lean_Language_Snapshot_Diagnostics_empty___closed__1 = _init_l_Lean_Language_Snapshot_Diagnostics_empty___closed__1();
lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty___closed__1);
l_Lean_Language_Snapshot_Diagnostics_empty = _init_l_Lean_Language_Snapshot_Diagnostics_empty();
lean_mark_persistent(l_Lean_Language_Snapshot_Diagnostics_empty);
l_Lean_Language_Snapshot_desc___autoParam___closed__0 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__0();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__0);
l_Lean_Language_Snapshot_desc___autoParam___closed__1 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__1();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__1);
l_Lean_Language_Snapshot_desc___autoParam___closed__2 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__2();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__2);
l_Lean_Language_Snapshot_desc___autoParam___closed__3 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__3();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__3);
l_Lean_Language_Snapshot_desc___autoParam___closed__4 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__4();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__4);
l_Lean_Language_Snapshot_desc___autoParam___closed__5 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__5();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__5);
l_Lean_Language_Snapshot_desc___autoParam___closed__6 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__6();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__6);
l_Lean_Language_Snapshot_desc___autoParam___closed__7 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__7();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__7);
l_Lean_Language_Snapshot_desc___autoParam___closed__8 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__8();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__8);
l_Lean_Language_Snapshot_desc___autoParam___closed__9 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__9();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__9);
l_Lean_Language_Snapshot_desc___autoParam___closed__10 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__10();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__10);
l_Lean_Language_Snapshot_desc___autoParam___closed__11 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__11();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__11);
l_Lean_Language_Snapshot_desc___autoParam___closed__12 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__12();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__12);
l_Lean_Language_Snapshot_desc___autoParam___closed__13 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__13();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__13);
l_Lean_Language_Snapshot_desc___autoParam___closed__14 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__14();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__14);
l_Lean_Language_Snapshot_desc___autoParam___closed__15 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__15();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__15);
l_Lean_Language_Snapshot_desc___autoParam___closed__16 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__16();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__16);
l_Lean_Language_Snapshot_desc___autoParam___closed__17 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__17();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__17);
l_Lean_Language_Snapshot_desc___autoParam___closed__18 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__18();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__18);
l_Lean_Language_Snapshot_desc___autoParam___closed__19 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__19();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__19);
l_Lean_Language_Snapshot_desc___autoParam___closed__20 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__20();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__20);
l_Lean_Language_Snapshot_desc___autoParam___closed__21 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__21();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__21);
l_Lean_Language_Snapshot_desc___autoParam___closed__22 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__22();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__22);
l_Lean_Language_Snapshot_desc___autoParam___closed__23 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__23();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__23);
l_Lean_Language_Snapshot_desc___autoParam___closed__24 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__24();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__24);
l_Lean_Language_Snapshot_desc___autoParam___closed__25 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__25();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__25);
l_Lean_Language_Snapshot_desc___autoParam___closed__26 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__26();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__26);
l_Lean_Language_Snapshot_desc___autoParam___closed__27 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__27();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__27);
l_Lean_Language_Snapshot_desc___autoParam___closed__28 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__28();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__28);
l_Lean_Language_Snapshot_desc___autoParam___closed__29 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__29();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__29);
l_Lean_Language_Snapshot_desc___autoParam___closed__30 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__30();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__30);
l_Lean_Language_Snapshot_desc___autoParam___closed__31 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__31();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__31);
l_Lean_Language_Snapshot_desc___autoParam___closed__32 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__32();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__32);
l_Lean_Language_Snapshot_desc___autoParam___closed__33 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__33();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__33);
l_Lean_Language_Snapshot_desc___autoParam___closed__34 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__34();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__34);
l_Lean_Language_Snapshot_desc___autoParam___closed__35 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__35();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__35);
l_Lean_Language_Snapshot_desc___autoParam___closed__36 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__36();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__36);
l_Lean_Language_Snapshot_desc___autoParam___closed__37 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__37();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__37);
l_Lean_Language_Snapshot_desc___autoParam___closed__38 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__38();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__38);
l_Lean_Language_Snapshot_desc___autoParam___closed__39 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__39();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__39);
l_Lean_Language_Snapshot_desc___autoParam___closed__40 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__40();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__40);
l_Lean_Language_Snapshot_desc___autoParam___closed__41 = _init_l_Lean_Language_Snapshot_desc___autoParam___closed__41();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam___closed__41);
l_Lean_Language_Snapshot_desc___autoParam = _init_l_Lean_Language_Snapshot_desc___autoParam();
lean_mark_persistent(l_Lean_Language_Snapshot_desc___autoParam);
l_Lean_Language_instInhabitedSnapshot_default___closed__0 = _init_l_Lean_Language_instInhabitedSnapshot_default___closed__0();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot_default___closed__0);
l_Lean_Language_instInhabitedSnapshot_default___closed__1 = _init_l_Lean_Language_instInhabitedSnapshot_default___closed__1();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot_default___closed__1);
l_Lean_Language_instInhabitedSnapshot_default___closed__2 = _init_l_Lean_Language_instInhabitedSnapshot_default___closed__2();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot_default___closed__2);
l_Lean_Language_instInhabitedSnapshot_default = _init_l_Lean_Language_instInhabitedSnapshot_default();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot_default);
l_Lean_Language_instInhabitedSnapshot = _init_l_Lean_Language_instInhabitedSnapshot();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshot);
l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default = _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default();
lean_mark_persistent(l_Lean_Language_SnapshotTask_instInhabitedReportingRange_default);
l_Lean_Language_SnapshotTask_instInhabitedReportingRange = _init_l_Lean_Language_SnapshotTask_instInhabitedReportingRange();
lean_mark_persistent(l_Lean_Language_SnapshotTask_instInhabitedReportingRange);
l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0 = _init_l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0();
lean_mark_persistent(l_Lean_Language_SnapshotTask_defaultReportingRange___closed__0);
l_Lean_Language_instInhabitedSnapshotTree_default___closed__0 = _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__0();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree_default___closed__0);
l_Lean_Language_instInhabitedSnapshotTree_default___closed__1 = _init_l_Lean_Language_instInhabitedSnapshotTree_default___closed__1();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree_default___closed__1);
l_Lean_Language_instInhabitedSnapshotTree_default = _init_l_Lean_Language_instInhabitedSnapshotTree_default();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree_default);
l_Lean_Language_instInhabitedSnapshotTree = _init_l_Lean_Language_instInhabitedSnapshotTree();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotTree);
l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_ = _init_l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_();
lean_mark_persistent(l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_);
l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_ = _init_l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_();
lean_mark_persistent(l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_);
l_Lean_Language_instImpl___closed__2____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_ = _init_l_Lean_Language_instImpl___closed__2____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_();
lean_mark_persistent(l_Lean_Language_instImpl___closed__2____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_);
l_Lean_Language_instImpl____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_ = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic_3470488393____hygCtx___hyg_52_);
l_Lean_Language_instTypeNameSnapshotTree = _init_l_Lean_Language_instTypeNameSnapshotTree();
lean_mark_persistent(l_Lean_Language_instTypeNameSnapshotTree);
l_Lean_Language_instToSnapshotTreeSnapshotTree = _init_l_Lean_Language_instToSnapshotTreeSnapshotTree();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeSnapshotTree);
l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0 = _init_l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0();
lean_mark_persistent(l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__0);
l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__1 = _init_l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__1();
lean_mark_persistent(l_Lean_Language_SnapshotTask_cancelRec___redArg___closed__1);
l_Lean_Language_instInhabitedSnapshotLeaf_default = _init_l_Lean_Language_instInhabitedSnapshotLeaf_default();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotLeaf_default);
l_Lean_Language_instInhabitedSnapshotLeaf = _init_l_Lean_Language_instInhabitedSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instInhabitedSnapshotLeaf);
l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_ = _init_l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_();
lean_mark_persistent(l_Lean_Language_instImpl___closed__0____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_);
l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_ = _init_l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_();
lean_mark_persistent(l_Lean_Language_instImpl___closed__1____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_);
l_Lean_Language_instImpl____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_ = _init_l_Lean_Language_instImpl____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_();
lean_mark_persistent(l_Lean_Language_instImpl____x40_Lean_Language_Basic_3093936625____hygCtx___hyg_30_);
l_Lean_Language_instTypeNameSnapshotLeaf = _init_l_Lean_Language_instTypeNameSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instTypeNameSnapshotLeaf);
l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0 = _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeSnapshotLeaf___lam__0___closed__0);
l_Lean_Language_instToSnapshotTreeSnapshotLeaf = _init_l_Lean_Language_instToSnapshotTreeSnapshotLeaf();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeSnapshotLeaf);
l_Lean_Language_instToSnapshotTreeDynamicSnapshot = _init_l_Lean_Language_instToSnapshotTreeDynamicSnapshot();
lean_mark_persistent(l_Lean_Language_instToSnapshotTreeDynamicSnapshot);
l_Lean_Language_instInhabitedDynamicSnapshot___closed__0 = _init_l_Lean_Language_instInhabitedDynamicSnapshot___closed__0();
lean_mark_persistent(l_Lean_Language_instInhabitedDynamicSnapshot___closed__0);
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
l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Language_initFn____x40_Lean_Language_Basic_1801653074____hygCtx___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_printMessageEndPos = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_printMessageEndPos);
lean_dec_ref(res);
}l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__0____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__1____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__2____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__3____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_);
l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_ = _init_l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Language_initFn___closed__4____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Language_initFn____x40_Lean_Language_Basic_709047587____hygCtx___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Language_maxErrors = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Language_maxErrors);
lean_dec_ref(res);
}l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__1);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at_____private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4_spec__4_spec__5___closed__2);
l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0 = _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0();
lean_mark_persistent(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___Lean_PersistentArray_foldlM___at_____private_Lean_Language_Basic_0__Lean_Language_reportMessages_spec__4_spec__4___closed__0);
l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___closed__0 = _init_l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___closed__0();
lean_mark_persistent(l___private_Lean_Language_Basic_0__Lean_Language_reportMessages___closed__0);
l_Lean_Language_SnapshotTree_getAll___closed__0 = _init_l_Lean_Language_SnapshotTree_getAll___closed__0();
lean_mark_persistent(l_Lean_Language_SnapshotTree_getAll___closed__0);
l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0 = _init_l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0();
lean_mark_persistent(l___private_Lean_Language_Basic_0__Lean_Language_SnapshotTree_waitAll_go___closed__0);
l_Lean_Language_instMonadLiftProcessingMProcessingTIO = _init_l_Lean_Language_instMonadLiftProcessingMProcessingTIO();
lean_mark_persistent(l_Lean_Language_instMonadLiftProcessingMProcessingTIO);
l_Lean_Language_diagnosticsOfHeaderError___closed__0 = _init_l_Lean_Language_diagnosticsOfHeaderError___closed__0();
lean_mark_persistent(l_Lean_Language_diagnosticsOfHeaderError___closed__0);
l_Lean_Language_diagnosticsOfHeaderError___closed__1 = _init_l_Lean_Language_diagnosticsOfHeaderError___closed__1();
lean_mark_persistent(l_Lean_Language_diagnosticsOfHeaderError___closed__1);
l_Lean_Language_withHeaderExceptions___redArg___closed__0 = _init_l_Lean_Language_withHeaderExceptions___redArg___closed__0();
lean_mark_persistent(l_Lean_Language_withHeaderExceptions___redArg___closed__0);
l_Lean_Language_withHeaderExceptions___redArg___closed__1 = _init_l_Lean_Language_withHeaderExceptions___redArg___closed__1();
lean_mark_persistent(l_Lean_Language_withHeaderExceptions___redArg___closed__1);
l_Lean_Language_withHeaderExceptions___redArg___closed__2 = _init_l_Lean_Language_withHeaderExceptions___redArg___closed__2();
lean_mark_persistent(l_Lean_Language_withHeaderExceptions___redArg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
