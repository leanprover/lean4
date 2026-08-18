// Lean compiler output
// Module: Lean.Elab.Frontend
// Imports: import Init.System.Platform public import Lean.Language.Lean public import Lean.Server.References public import Lean.Util.Profiler import Lean.Compiler.Options import Lean.Compiler.InitAttr import Lean.Linter.PersistentLintLog import Lean.Util.ProfilerServer
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_runInitAttrsForModules(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_ModuleArtifacts_oleanParts(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_compacted_region_read(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_ModuleArtifacts_irParts(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleArtifacts_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_load_dynlib(lean_object*);
uint32_t lean_internal_get_hardware_concurrency(lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Linter_recordLints(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_writeModule(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_getRegularInitAttrModIdxs(lean_object*);
lean_object* lean_compacted_region_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*);
lean_object* l_Lean_Language_Lean_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
lean_object* l_IO_FS_readFile(lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_io_getenv(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed(lean_object*, lean_object*);
lean_object* lean_enable_initializer_execution();
lean_object* l_Lean_Parser_mkInputContext___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler_output;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Firefox_Profile_export(lean_object*, double, lean_object*, lean_object*);
lean_object* l_Lean_Firefox_instToJsonProfile_toJson(lean_object*);
extern lean_object* l_Lean_trace_profiler_serve;
lean_object* l_Lean_Firefox_Profile_serve(lean_object*);
lean_object* l_Lean_Server_findModuleRefs(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Server_ModuleRefs_toLspModuleRefs(lean_object*);
lean_object* l_Lean_Server_collectImports(lean_object*);
lean_object* l_Lean_Server_instToJsonIlean_toJson(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_displayStats(lean_object*);
lean_object* l_Lean_Language_Lean_truncateToHeader(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_process(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_internal_cmdlineSnapshots;
extern lean_object* l_Lean_Elab_async;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_finished___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(lean_object*);
lean_object* l_Lean_withImporting___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unexpected internal error: "};
static const lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Frontend_processCommand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "parsing"};
static const lean_object* l_Lean_Elab_Frontend_processCommand___closed__0 = (const lean_object*)&l_Lean_Elab_Frontend_processCommand___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_IO_processCommandsIncrementally___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_IO_processCommandsIncrementally___closed__0 = (const lean_object*)&l_Lean_Elab_IO_processCommandsIncrementally___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_process___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_process___closed__0 = (const lean_object*)&l_Lean_Elab_process___closed__0_value;
static const lean_string_object l_Lean_Elab_process___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "<input>"};
static const lean_object* l_Lean_Elab_process___closed__1 = (const lean_object*)&l_Lean_Elab_process___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.Data.DHashMap.Internal.Defs"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 37, .m_data = "Std.DHashMap.Internal.Raw₀.Const.get!"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "server"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object*);
static const lean_string_object l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "deps"};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "failed to parse snapshot deps file "};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4;
static const lean_string_object l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "LEAN_IMPORT_WORKERS"};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_snap"};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__0 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 190, 236, 193, 206, 64, 207, 210)}};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_runFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__0_value;
static lean_once_cell_t l_Lean_Elab_runFrontend___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_runFrontend___closed__1;
static const lean_string_object l_Lean_Elab_runFrontend___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ".olean serialization"};
static const lean_object* l_Lean_Elab_runFrontend___closed__2 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg(lean_object* v_commandState_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_parserState_5_; lean_object* v_cmdPos_6_; lean_object* v_commands_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_17_; 
v___x_4_ = lean_st_ref_take(v_a_2_);
v_parserState_5_ = lean_ctor_get(v___x_4_, 1);
v_cmdPos_6_ = lean_ctor_get(v___x_4_, 2);
v_commands_7_ = lean_ctor_get(v___x_4_, 3);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_4_);
if (v_isSharedCheck_17_ == 0)
{
lean_object* v_unused_18_; 
v_unused_18_ = lean_ctor_get(v___x_4_, 0);
lean_dec(v_unused_18_);
v___x_9_ = v___x_4_;
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_commands_7_);
lean_inc(v_cmdPos_6_);
lean_inc(v_parserState_5_);
lean_dec(v___x_4_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_17_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 0, v_commandState_1_);
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_commandState_1_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_parserState_5_);
lean_ctor_set(v_reuseFailAlloc_16_, 2, v_cmdPos_6_);
lean_ctor_set(v_reuseFailAlloc_16_, 3, v_commands_7_);
v___x_12_ = v_reuseFailAlloc_16_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_13_ = lean_st_ref_put(v_a_2_, v___x_12_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___redArg___boxed(lean_object* v_commandState_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Frontend_setCommandState___redArg(v_commandState_19_, v_a_20_);
lean_dec(v_a_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState(lean_object* v_commandState_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Elab_Frontend_setCommandState___redArg(v_commandState_23_, v_a_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setCommandState___boxed(lean_object* v_commandState_28_, lean_object* v_a_29_, lean_object* v_a_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_Frontend_setCommandState(v_commandState_28_, v_a_29_, v_a_30_);
lean_dec(v_a_30_);
lean_dec_ref(v_a_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg(lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; lean_object* v_commandState_39_; lean_object* v_cmdPos_40_; lean_object* v___x_41_; lean_object* v_fileName_42_; lean_object* v_fileMap_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_38_ = lean_st_ref_get(v_a_36_);
v_commandState_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_commandState_39_);
v_cmdPos_40_ = lean_ctor_get(v___x_38_, 2);
lean_inc(v_cmdPos_40_);
lean_dec(v___x_38_);
v___x_41_ = lean_st_mk_ref(v_commandState_39_);
v_fileName_42_ = lean_ctor_get(v_a_35_, 1);
v_fileMap_43_ = lean_ctor_get(v_a_35_, 2);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_box(0);
v___x_46_ = lean_box(0);
v___x_47_ = l_Lean_firstFrontendMacroScope;
v___x_48_ = lean_box(0);
v___x_49_ = 0;
lean_inc_ref(v_fileMap_43_);
lean_inc_ref(v_fileName_42_);
v___x_50_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_50_, 0, v_fileName_42_);
lean_ctor_set(v___x_50_, 1, v_fileMap_43_);
lean_ctor_set(v___x_50_, 2, v___x_44_);
lean_ctor_set(v___x_50_, 3, v_cmdPos_40_);
lean_ctor_set(v___x_50_, 4, v___x_45_);
lean_ctor_set(v___x_50_, 5, v___x_46_);
lean_ctor_set(v___x_50_, 6, v___x_47_);
lean_ctor_set(v___x_50_, 7, v___x_48_);
lean_ctor_set(v___x_50_, 8, v___x_46_);
lean_ctor_set(v___x_50_, 9, v___x_46_);
lean_ctor_set_uint8(v___x_50_, sizeof(void*)*10, v___x_49_);
lean_inc(v___x_41_);
v___x_51_ = lean_apply_3(v_x_34_, v___x_50_, v___x_41_, lean_box(0));
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 1);
v___x_53_ = lean_st_ref_get(v___x_41_);
lean_dec(v___x_41_);
v___x_54_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_53_, v_a_36_);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_61_ == 0)
{
lean_object* v_unused_62_; 
v_unused_62_ = lean_ctor_get(v___x_54_, 0);
lean_dec(v_unused_62_);
v___x_56_ = v___x_54_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_dec(v___x_54_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v_a_52_);
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_52_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_75_; 
lean_dec(v___x_41_);
v_a_63_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_75_ == 0)
{
v___x_65_ = v___x_51_;
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_51_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_67_ = l_Lean_Exception_toMessageData(v_a_63_);
v___x_68_ = l_Lean_MessageData_toString(v___x_67_);
v___x_69_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_70_ = lean_string_append(v___x_69_, v___x_68_);
lean_dec_ref(v___x_68_);
v___x_71_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_71_);
v___x_73_ = v___x_65_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___redArg___boxed(lean_object* v_x_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Elab_Frontend_runCommandElabM___redArg(v_x_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM(lean_object* v_00_u03b1_81_, lean_object* v_x_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; lean_object* v_commandState_87_; lean_object* v_cmdPos_88_; lean_object* v___x_89_; lean_object* v_fileName_90_; lean_object* v_fileMap_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_86_ = lean_st_ref_get(v_a_84_);
v_commandState_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc_ref(v_commandState_87_);
v_cmdPos_88_ = lean_ctor_get(v___x_86_, 2);
lean_inc(v_cmdPos_88_);
lean_dec(v___x_86_);
v___x_89_ = lean_st_mk_ref(v_commandState_87_);
v_fileName_90_ = lean_ctor_get(v_a_83_, 1);
v_fileMap_91_ = lean_ctor_get(v_a_83_, 2);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_box(0);
v___x_94_ = lean_box(0);
v___x_95_ = l_Lean_firstFrontendMacroScope;
v___x_96_ = lean_box(0);
v___x_97_ = 0;
lean_inc_ref(v_fileMap_91_);
lean_inc_ref(v_fileName_90_);
v___x_98_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_98_, 0, v_fileName_90_);
lean_ctor_set(v___x_98_, 1, v_fileMap_91_);
lean_ctor_set(v___x_98_, 2, v___x_92_);
lean_ctor_set(v___x_98_, 3, v_cmdPos_88_);
lean_ctor_set(v___x_98_, 4, v___x_93_);
lean_ctor_set(v___x_98_, 5, v___x_94_);
lean_ctor_set(v___x_98_, 6, v___x_95_);
lean_ctor_set(v___x_98_, 7, v___x_96_);
lean_ctor_set(v___x_98_, 8, v___x_94_);
lean_ctor_set(v___x_98_, 9, v___x_94_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*10, v___x_97_);
lean_inc(v___x_89_);
v___x_99_ = lean_apply_3(v_x_82_, v___x_98_, v___x_89_, lean_box(0));
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_99_, 1);
v___x_101_ = lean_st_ref_get(v___x_89_);
lean_dec(v___x_89_);
v___x_102_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_101_, v_a_84_);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v___x_102_, 0);
lean_dec(v_unused_110_);
v___x_104_ = v___x_102_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_dec(v___x_102_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_a_100_);
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_100_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_123_; 
lean_dec(v___x_89_);
v_a_111_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_123_ == 0)
{
v___x_113_ = v___x_99_;
v_isShared_114_ = v_isSharedCheck_123_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_99_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_123_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_115_ = l_Lean_Exception_toMessageData(v_a_111_);
v___x_116_ = l_Lean_MessageData_toString(v___x_115_);
v___x_117_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_118_ = lean_string_append(v___x_117_, v___x_116_);
lean_dec_ref(v___x_116_);
v___x_119_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_119_);
v___x_121_ = v___x_113_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_runCommandElabM___boxed(lean_object* v_00_u03b1_124_, lean_object* v_x_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Elab_Frontend_runCommandElabM(v_00_u03b1_124_, v_x_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* v_stx_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v___x_136_; lean_object* v_commandState_137_; lean_object* v_cmdPos_138_; lean_object* v___x_139_; lean_object* v_fileName_140_; lean_object* v_fileMap_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_136_ = lean_st_ref_get(v_a_134_);
v_commandState_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_commandState_137_);
v_cmdPos_138_ = lean_ctor_get(v___x_136_, 2);
lean_inc(v_cmdPos_138_);
lean_dec(v___x_136_);
v___x_139_ = lean_st_mk_ref(v_commandState_137_);
v_fileName_140_ = lean_ctor_get(v_a_133_, 1);
v_fileMap_141_ = lean_ctor_get(v_a_133_, 2);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = ((lean_object*)(l_Lean_Elab_Frontend_elabCommandAtFrontend___closed__0));
v___x_144_ = lean_box(0);
v___x_145_ = lean_box(0);
v___x_146_ = l_Lean_firstFrontendMacroScope;
v___x_147_ = lean_box(0);
v___x_148_ = 0;
lean_inc_ref(v_fileMap_141_);
lean_inc_ref(v_fileName_140_);
v___x_149_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_149_, 0, v_fileName_140_);
lean_ctor_set(v___x_149_, 1, v_fileMap_141_);
lean_ctor_set(v___x_149_, 2, v___x_142_);
lean_ctor_set(v___x_149_, 3, v_cmdPos_138_);
lean_ctor_set(v___x_149_, 4, v___x_144_);
lean_ctor_set(v___x_149_, 5, v___x_145_);
lean_ctor_set(v___x_149_, 6, v___x_146_);
lean_ctor_set(v___x_149_, 7, v___x_147_);
lean_ctor_set(v___x_149_, 8, v___x_145_);
lean_ctor_set(v___x_149_, 9, v___x_145_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*10, v___x_148_);
v___x_150_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_132_, v___x_143_, v___x_149_, v___x_139_);
lean_dec_ref_known(v___x_149_, 10);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_a_151_);
lean_dec_ref_known(v___x_150_, 1);
v___x_152_ = lean_st_ref_get(v___x_139_);
lean_dec(v___x_139_);
v___x_153_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_152_, v_a_134_);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_153_, 0);
lean_dec(v_unused_161_);
v___x_155_ = v___x_153_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_dec(v___x_153_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v_a_151_);
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_151_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_174_; 
lean_dec(v___x_139_);
v_a_162_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_174_ == 0)
{
v___x_164_ = v___x_150_;
v_isShared_165_ = v_isSharedCheck_174_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_150_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_174_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_166_ = l_Lean_Exception_toMessageData(v_a_162_);
v___x_167_ = l_Lean_MessageData_toString(v___x_166_);
v___x_168_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_169_ = lean_string_append(v___x_168_, v___x_167_);
lean_dec_ref(v___x_167_);
v___x_170_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_170_);
v___x_172_ = v___x_164_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object* v_stx_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_stx_175_, v_a_176_, v_a_177_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg(lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; lean_object* v_parserState_183_; lean_object* v_commandState_184_; lean_object* v_commands_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_196_; 
v___x_182_ = lean_st_ref_take(v_a_180_);
v_parserState_183_ = lean_ctor_get(v___x_182_, 1);
v_commandState_184_ = lean_ctor_get(v___x_182_, 0);
v_commands_185_ = lean_ctor_get(v___x_182_, 3);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v___x_182_, 2);
lean_dec(v_unused_197_);
v___x_187_ = v___x_182_;
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_commands_185_);
lean_inc(v_parserState_183_);
lean_inc(v_commandState_184_);
lean_dec(v___x_182_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_196_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_pos_189_; lean_object* v___x_191_; 
v_pos_189_ = lean_ctor_get(v_parserState_183_, 0);
lean_inc(v_pos_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 2, v_pos_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_commandState_184_);
lean_ctor_set(v_reuseFailAlloc_195_, 1, v_parserState_183_);
lean_ctor_set(v_reuseFailAlloc_195_, 2, v_pos_189_);
lean_ctor_set(v_reuseFailAlloc_195_, 3, v_commands_185_);
v___x_191_ = v_reuseFailAlloc_195_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_st_ref_put(v_a_180_, v___x_191_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_198_);
lean_dec(v_a_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Elab_Frontend_updateCmdPos(v_a_205_, v_a_206_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg(lean_object* v_a_209_){
_start:
{
lean_object* v___x_211_; lean_object* v_parserState_212_; lean_object* v___x_213_; 
v___x_211_ = lean_st_ref_get(v_a_209_);
v_parserState_212_ = lean_ctor_get(v___x_211_, 1);
lean_inc_ref(v_parserState_212_);
lean_dec(v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v_parserState_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg___boxed(lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_214_);
lean_dec(v_a_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Elab_Frontend_getParserState(v_a_221_, v_a_222_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg(lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; lean_object* v_commandState_228_; lean_object* v___x_229_; 
v___x_227_ = lean_st_ref_get(v_a_225_);
v_commandState_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc_ref(v_commandState_228_);
lean_dec(v___x_227_);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v_commandState_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg___boxed(lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_230_);
lean_dec(v_a_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Elab_Frontend_getCommandState(v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg(lean_object* v_ps_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; lean_object* v_commandState_245_; lean_object* v_cmdPos_246_; lean_object* v_commands_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_257_; 
v___x_244_ = lean_st_ref_take(v_a_242_);
v_commandState_245_ = lean_ctor_get(v___x_244_, 0);
v_cmdPos_246_ = lean_ctor_get(v___x_244_, 2);
v_commands_247_ = lean_ctor_get(v___x_244_, 3);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_244_, 1);
lean_dec(v_unused_258_);
v___x_249_ = v___x_244_;
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_commands_247_);
lean_inc(v_cmdPos_246_);
lean_inc(v_commandState_245_);
lean_dec(v___x_244_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v_ps_241_);
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_commandState_245_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_ps_241_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_cmdPos_246_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v_commands_247_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_st_ref_put(v_a_242_, v___x_252_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg___boxed(lean_object* v_ps_259_, lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_259_, v_a_260_);
lean_dec(v_a_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object* v_ps_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_263_, v_a_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object* v_ps_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Elab_Frontend_setParserState(v_ps_268_, v_a_269_, v_a_270_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg(lean_object* v_msgs_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; lean_object* v_commandState_277_; lean_object* v_parserState_278_; lean_object* v_cmdPos_279_; lean_object* v_commands_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_309_; 
v___x_276_ = lean_st_ref_take(v_a_274_);
v_commandState_277_ = lean_ctor_get(v___x_276_, 0);
v_parserState_278_ = lean_ctor_get(v___x_276_, 1);
v_cmdPos_279_ = lean_ctor_get(v___x_276_, 2);
v_commands_280_ = lean_ctor_get(v___x_276_, 3);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_309_ == 0)
{
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_309_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_commands_280_);
lean_inc(v_cmdPos_279_);
lean_inc(v_parserState_278_);
lean_inc(v_commandState_277_);
lean_dec(v___x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_309_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_env_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v_prevLinterStates_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_307_; 
v_env_284_ = lean_ctor_get(v_commandState_277_, 0);
v_scopes_285_ = lean_ctor_get(v_commandState_277_, 2);
v_usedQuotCtxts_286_ = lean_ctor_get(v_commandState_277_, 3);
v_nextMacroScope_287_ = lean_ctor_get(v_commandState_277_, 4);
v_maxRecDepth_288_ = lean_ctor_get(v_commandState_277_, 5);
v_ngen_289_ = lean_ctor_get(v_commandState_277_, 6);
v_auxDeclNGen_290_ = lean_ctor_get(v_commandState_277_, 7);
v_infoState_291_ = lean_ctor_get(v_commandState_277_, 8);
v_traceState_292_ = lean_ctor_get(v_commandState_277_, 9);
v_snapshotTasks_293_ = lean_ctor_get(v_commandState_277_, 10);
v_prevLinterStates_294_ = lean_ctor_get(v_commandState_277_, 11);
v_isSharedCheck_307_ = !lean_is_exclusive(v_commandState_277_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v_commandState_277_, 1);
lean_dec(v_unused_308_);
v___x_296_ = v_commandState_277_;
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_prevLinterStates_294_);
lean_inc(v_snapshotTasks_293_);
lean_inc(v_traceState_292_);
lean_inc(v_infoState_291_);
lean_inc(v_auxDeclNGen_290_);
lean_inc(v_ngen_289_);
lean_inc(v_maxRecDepth_288_);
lean_inc(v_nextMacroScope_287_);
lean_inc(v_usedQuotCtxts_286_);
lean_inc(v_scopes_285_);
lean_inc(v_env_284_);
lean_dec(v_commandState_277_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_307_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v_msgs_273_);
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_env_284_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_msgs_273_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_306_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_306_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_306_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_306_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_306_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_306_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_306_, 10, v_snapshotTasks_293_);
lean_ctor_set(v_reuseFailAlloc_306_, 11, v_prevLinterStates_294_);
v___x_299_ = v_reuseFailAlloc_306_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_299_);
v___x_301_ = v___x_282_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_parserState_278_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_cmdPos_279_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_commands_280_);
v___x_301_ = v_reuseFailAlloc_305_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_st_ref_put(v_a_274_, v___x_301_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
return v___x_304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* v_msgs_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_310_, v_a_311_);
lean_dec(v_a_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* v_msgs_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_314_, v_a_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* v_msgs_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Elab_Frontend_setMessages(v_msgs_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* v_a_324_){
_start:
{
lean_object* v___x_326_; 
lean_inc_ref(v_a_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v_a_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_327_);
lean_dec_ref(v_a_327_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; 
lean_inc_ref(v_a_330_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v_a_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Elab_Frontend_getInputContext(v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_338_, lean_object* v___x_339_, lean_object* v_a_340_, lean_object* v_messages_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
lean_inc_ref(v_a_338_);
v___x_343_ = l_Lean_Parser_parseCommand(v_a_338_, v___x_339_, v_a_340_, v_messages_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* v_a_344_, lean_object* v___x_345_, lean_object* v_a_346_, lean_object* v_messages_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Elab_Frontend_processCommand___lam__0(v_a_344_, v___x_345_, v_a_346_, v_messages_347_, v_x_348_);
lean_dec_ref(v_a_344_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v_env_359_; lean_object* v_messages_360_; lean_object* v_scopes_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v_opts_364_; lean_object* v_currNamespace_365_; lean_object* v_openDecls_366_; lean_object* v___x_367_; lean_object* v___f_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_snd_372_; lean_object* v_fst_373_; lean_object* v_fst_374_; lean_object* v_snd_375_; lean_object* v___x_376_; lean_object* v_commandState_377_; lean_object* v_parserState_378_; lean_object* v_cmdPos_379_; lean_object* v_commands_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_410_; 
v___x_354_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_352_);
lean_dec_ref(v___x_354_);
v___x_355_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_352_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_355_);
v___x_357_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_352_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
v_env_359_ = lean_ctor_get(v_a_356_, 0);
lean_inc_ref(v_env_359_);
v_messages_360_ = lean_ctor_get(v_a_356_, 1);
lean_inc_ref(v_messages_360_);
v_scopes_361_ = lean_ctor_get(v_a_356_, 2);
lean_inc(v_scopes_361_);
lean_dec(v_a_356_);
v___x_362_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_363_ = l_List_head_x21___redArg(v___x_362_, v_scopes_361_);
lean_dec(v_scopes_361_);
v_opts_364_ = lean_ctor_get(v___x_363_, 1);
lean_inc_ref_n(v_opts_364_, 2);
v_currNamespace_365_ = lean_ctor_get(v___x_363_, 2);
lean_inc(v_currNamespace_365_);
v_openDecls_366_ = lean_ctor_get(v___x_363_, 3);
lean_inc(v_openDecls_366_);
lean_dec(v___x_363_);
v___x_367_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_367_, 0, v_env_359_);
lean_ctor_set(v___x_367_, 1, v_opts_364_);
lean_ctor_set(v___x_367_, 2, v_currNamespace_365_);
lean_ctor_set(v___x_367_, 3, v_openDecls_366_);
lean_inc_ref(v_a_351_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_368_, 0, v_a_351_);
lean_closure_set(v___f_368_, 1, v___x_367_);
lean_closure_set(v___f_368_, 2, v_a_358_);
lean_closure_set(v___f_368_, 3, v_messages_360_);
v___x_369_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_370_ = lean_box(0);
v___x_371_ = lean_profileit(v___x_369_, v_opts_364_, v___f_368_, v___x_370_);
lean_dec_ref(v_opts_364_);
v_snd_372_ = lean_ctor_get(v___x_371_, 1);
lean_inc(v_snd_372_);
v_fst_373_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_fst_373_);
lean_dec(v___x_371_);
v_fst_374_ = lean_ctor_get(v_snd_372_, 0);
lean_inc(v_fst_374_);
v_snd_375_ = lean_ctor_get(v_snd_372_, 1);
lean_inc(v_snd_375_);
lean_dec(v_snd_372_);
v___x_376_ = lean_st_ref_take(v_a_352_);
v_commandState_377_ = lean_ctor_get(v___x_376_, 0);
v_parserState_378_ = lean_ctor_get(v___x_376_, 1);
v_cmdPos_379_ = lean_ctor_get(v___x_376_, 2);
v_commands_380_ = lean_ctor_get(v___x_376_, 3);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_410_ == 0)
{
v___x_382_ = v___x_376_;
v_isShared_383_ = v_isSharedCheck_410_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_commands_380_);
lean_inc(v_cmdPos_379_);
lean_inc(v_parserState_378_);
lean_inc(v_commandState_377_);
lean_dec(v___x_376_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_410_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_inc(v_fst_373_);
v___x_384_ = lean_array_push(v_commands_380_, v_fst_373_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 3, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_commandState_377_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_parserState_378_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_cmdPos_379_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v___x_384_);
v___x_386_ = v_reuseFailAlloc_409_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_st_ref_put(v_a_352_, v___x_386_);
v___x_388_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_374_, v_a_352_);
lean_dec_ref(v___x_388_);
v___x_389_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_375_, v_a_352_);
lean_dec_ref(v___x_389_);
lean_inc(v_fst_373_);
v___x_390_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_373_, v_a_351_, v_a_352_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_399_; 
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_400_);
v___x_392_ = v___x_390_;
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
else
{
lean_dec(v___x_390_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = l_Lean_Parser_isTerminalCommand(v_fst_373_);
v___x_395_ = lean_box(v___x_394_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec(v_fst_373_);
v_a_401_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_390_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_390_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_Frontend_processCommand(v_a_411_, v_a_412_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Elab_Frontend_processCommand(v_a_415_, v_a_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_429_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_429_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
uint8_t v___x_423_; 
v___x_423_ = lean_unbox(v_a_419_);
lean_dec(v_a_419_);
if (v___x_423_ == 0)
{
lean_del_object(v___x_421_);
goto _start;
}
else
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_box(0);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_425_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_418_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_418_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Elab_Frontend_processCommands(v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(lean_object* v_a_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_444_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_445_, size_t v_i_446_, size_t v_stop_447_, lean_object* v_b_448_){
_start:
{
lean_object* v___y_450_; uint8_t v___x_454_; 
v___x_454_ = lean_usize_dec_eq(v_i_446_, v_stop_447_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_array_uget_borrowed(v_as_445_, v_i_446_);
if (lean_obj_tag(v___x_455_) == 0)
{
v___y_450_ = v_b_448_;
goto v___jp_449_;
}
else
{
lean_object* v_val_456_; lean_object* v___x_457_; 
v_val_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_val_456_);
v___x_457_ = lean_array_push(v_b_448_, v_val_456_);
v___y_450_ = v___x_457_;
goto v___jp_449_;
}
}
else
{
return v_b_448_;
}
v___jp_449_:
{
size_t v___x_451_; size_t v___x_452_; 
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_add(v_i_446_, v___x_451_);
v_i_446_ = v___x_452_;
v_b_448_ = v___y_450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_458_, lean_object* v_i_459_, lean_object* v_stop_460_, lean_object* v_b_461_){
_start:
{
size_t v_i_boxed_462_; size_t v_stop_boxed_463_; lean_object* v_res_464_; 
v_i_boxed_462_ = lean_unbox_usize(v_i_459_);
lean_dec(v_i_459_);
v_stop_boxed_463_ = lean_unbox_usize(v_stop_460_);
lean_dec(v_stop_460_);
v_res_464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_458_, v_i_boxed_462_, v_stop_boxed_463_, v_b_461_);
lean_dec_ref(v_as_458_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_467_, lean_object* v_start_468_, lean_object* v_stop_469_){
_start:
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_471_ = lean_nat_dec_lt(v_start_468_, v_stop_469_);
if (v___x_471_ == 0)
{
return v___x_470_;
}
else
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = lean_array_get_size(v_as_467_);
v___x_473_ = lean_nat_dec_le(v_stop_469_, v___x_472_);
if (v___x_473_ == 0)
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_lt(v_start_468_, v___x_472_);
if (v___x_474_ == 0)
{
return v___x_470_;
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_usize_of_nat(v_start_468_);
v___x_476_ = lean_usize_of_nat(v___x_472_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_467_, v___x_475_, v___x_476_, v___x_470_);
return v___x_477_;
}
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_usize_of_nat(v_start_468_);
v___x_479_ = lean_usize_of_nat(v_stop_469_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_467_, v___x_478_, v___x_479_, v___x_470_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_481_, lean_object* v_start_482_, lean_object* v_stop_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_481_, v_start_482_, v_stop_483_);
lean_dec(v_stop_483_);
lean_dec(v_start_482_);
lean_dec_ref(v_as_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_485_, size_t v_i_486_, lean_object* v_bs_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_lt(v_i_486_, v_sz_485_);
if (v___x_488_ == 0)
{
return v_bs_487_;
}
else
{
lean_object* v_v_489_; lean_object* v_elabSnap_490_; lean_object* v_infoTreeSnap_491_; lean_object* v___x_492_; lean_object* v_infoTree_x3f_493_; lean_object* v___x_494_; lean_object* v_bs_x27_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v_v_489_ = lean_array_uget_borrowed(v_bs_487_, v_i_486_);
v_elabSnap_490_ = lean_ctor_get(v_v_489_, 3);
v_infoTreeSnap_491_ = lean_ctor_get(v_elabSnap_490_, 3);
lean_inc_ref(v_infoTreeSnap_491_);
v___x_492_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_491_);
v_infoTree_x3f_493_ = lean_ctor_get(v___x_492_, 2);
lean_inc(v_infoTree_x3f_493_);
lean_dec(v___x_492_);
v___x_494_ = lean_unsigned_to_nat(0u);
v_bs_x27_495_ = lean_array_uset(v_bs_487_, v_i_486_, v___x_494_);
v___x_496_ = ((size_t)1ULL);
v___x_497_ = lean_usize_add(v_i_486_, v___x_496_);
v___x_498_ = lean_array_uset(v_bs_x27_495_, v_i_486_, v_infoTree_x3f_493_);
v_i_486_ = v___x_497_;
v_bs_487_ = v___x_498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_500_, lean_object* v_i_501_, lean_object* v_bs_502_){
_start:
{
size_t v_sz_boxed_503_; size_t v_i_boxed_504_; lean_object* v_res_505_; 
v_sz_boxed_503_ = lean_unbox_usize(v_sz_500_);
lean_dec(v_sz_500_);
v_i_boxed_504_ = lean_unbox_usize(v_i_501_);
lean_dec(v_i_501_);
v_res_505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_503_, v_i_boxed_504_, v_bs_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_506_, size_t v_i_507_, lean_object* v_bs_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_509_ == 0)
{
return v_bs_508_;
}
else
{
lean_object* v_v_510_; lean_object* v_stx_511_; lean_object* v___x_512_; lean_object* v_bs_x27_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v_v_510_ = lean_array_uget_borrowed(v_bs_508_, v_i_507_);
v_stx_511_ = lean_ctor_get(v_v_510_, 1);
lean_inc(v_stx_511_);
v___x_512_ = lean_unsigned_to_nat(0u);
v_bs_x27_513_ = lean_array_uset(v_bs_508_, v_i_507_, v___x_512_);
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_507_, v___x_514_);
v___x_516_ = lean_array_uset(v_bs_x27_513_, v_i_507_, v_stx_511_);
v_i_507_ = v___x_515_;
v_bs_508_ = v___x_516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_bs_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_522_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_521_, v_i_boxed_522_, v_bs_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t v_sz_524_, size_t v_i_525_, lean_object* v_bs_526_){
_start:
{
uint8_t v___x_527_; 
v___x_527_ = lean_usize_dec_lt(v_i_525_, v_sz_524_);
if (v___x_527_ == 0)
{
return v_bs_526_;
}
else
{
lean_object* v_v_528_; lean_object* v_diagnostics_529_; lean_object* v_msgLog_530_; lean_object* v___x_531_; lean_object* v_bs_x27_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v_v_528_ = lean_array_uget_borrowed(v_bs_526_, v_i_525_);
v_diagnostics_529_ = lean_ctor_get(v_v_528_, 1);
v_msgLog_530_ = lean_ctor_get(v_diagnostics_529_, 0);
lean_inc_ref(v_msgLog_530_);
v___x_531_ = lean_unsigned_to_nat(0u);
v_bs_x27_532_ = lean_array_uset(v_bs_526_, v_i_525_, v___x_531_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_add(v_i_525_, v___x_533_);
v___x_535_ = lean_array_uset(v_bs_x27_532_, v_i_525_, v_msgLog_530_);
v_i_525_ = v___x_534_;
v_bs_526_ = v___x_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_bs_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_541_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_boxed_540_, v_i_boxed_541_, v_bs_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object* v_as_543_, size_t v_i_544_, size_t v_stop_545_, lean_object* v_b_546_){
_start:
{
uint8_t v___x_547_; 
v___x_547_ = lean_usize_dec_eq(v_i_544_, v_stop_545_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; size_t v___x_550_; size_t v___x_551_; 
v___x_548_ = lean_array_uget_borrowed(v_as_543_, v_i_544_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_MessageLog_append(v_b_546_, v___x_548_);
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_544_, v___x_550_);
v_i_544_ = v___x_551_;
v_b_546_ = v___x_549_;
goto _start;
}
else
{
return v_b_546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object* v_as_553_, lean_object* v_i_554_, lean_object* v_stop_555_, lean_object* v_b_556_){
_start:
{
size_t v_i_boxed_557_; size_t v_stop_boxed_558_; lean_object* v_res_559_; 
v_i_boxed_557_ = lean_unbox_usize(v_i_554_);
lean_dec(v_i_554_);
v_stop_boxed_558_ = lean_unbox_usize(v_stop_555_);
lean_dec(v_stop_555_);
v_res_559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v_as_553_, v_i_boxed_557_, v_stop_boxed_558_, v_b_556_);
lean_dec_ref(v_as_553_);
return v_res_559_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_unsigned_to_nat(32u);
v___x_561_ = lean_mk_empty_array_with_capacity(v___x_560_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_563_ = ((size_t)5ULL);
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_unsigned_to_nat(32u);
v___x_566_ = lean_mk_empty_array_with_capacity(v___x_565_);
v___x_567_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_568_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v___x_566_);
lean_ctor_set(v___x_568_, 2, v___x_564_);
lean_ctor_set(v___x_568_, 3, v___x_564_);
lean_ctor_set_usize(v___x_568_, 4, v___x_563_);
return v___x_568_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = l_Lean_NameSet_empty;
v___x_570_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
lean_ctor_set(v___x_571_, 2, v___x_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_572_, lean_object* v_initialSnap_573_, lean_object* v_t_574_, lean_object* v_commands_575_){
_start:
{
lean_object* v_snap_577_; lean_object* v_parserState_578_; lean_object* v_elabSnap_579_; lean_object* v_nextCmdSnap_x3f_580_; lean_object* v_commands_581_; 
v_snap_577_ = lean_task_get_own(v_t_574_);
v_parserState_578_ = lean_ctor_get(v_snap_577_, 2);
lean_inc_ref(v_parserState_578_);
v_elabSnap_579_ = lean_ctor_get(v_snap_577_, 3);
lean_inc_ref(v_elabSnap_579_);
v_nextCmdSnap_x3f_580_ = lean_ctor_get(v_snap_577_, 4);
lean_inc(v_nextCmdSnap_x3f_580_);
v_commands_581_ = lean_array_push(v_commands_575_, v_snap_577_);
if (lean_obj_tag(v_nextCmdSnap_x3f_580_) == 1)
{
lean_object* v_val_582_; lean_object* v_task_583_; 
lean_dec_ref(v_elabSnap_579_);
lean_dec_ref(v_parserState_578_);
v_val_582_ = lean_ctor_get(v_nextCmdSnap_x3f_580_, 0);
lean_inc(v_val_582_);
lean_dec_ref_known(v_nextCmdSnap_x3f_580_, 1);
v_task_583_ = lean_ctor_get(v_val_582_, 3);
lean_inc_ref(v_task_583_);
lean_dec(v_val_582_);
v_t_574_ = v_task_583_;
v_commands_575_ = v_commands_581_;
goto _start;
}
else
{
lean_object* v___x_585_; lean_object* v___y_587_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; size_t v_sz_634_; size_t v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
lean_dec(v_nextCmdSnap_x3f_580_);
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_573_);
v___x_632_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_initialSnap_573_);
v___x_633_ = l_Lean_Language_SnapshotTree_getAll(v___x_632_);
v_sz_634_ = lean_array_size(v___x_633_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_634_, v___x_635_, v___x_633_);
v___x_637_ = lean_array_get_size(v___x_636_);
v___x_638_ = lean_nat_dec_lt(v___x_585_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec_ref(v___x_636_);
v___y_587_ = v___x_631_;
goto v___jp_586_;
}
else
{
uint8_t v___x_639_; 
v___x_639_ = lean_nat_dec_le(v___x_637_, v___x_637_);
if (v___x_639_ == 0)
{
if (v___x_638_ == 0)
{
lean_dec_ref(v___x_636_);
v___y_587_ = v___x_631_;
goto v___jp_586_;
}
else
{
size_t v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_usize_of_nat(v___x_637_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_636_, v___x_635_, v___x_640_, v___x_631_);
lean_dec_ref(v___x_636_);
v___y_587_ = v___x_641_;
goto v___jp_586_;
}
}
else
{
size_t v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_usize_of_nat(v___x_637_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_636_, v___x_635_, v___x_642_, v___x_631_);
lean_dec_ref(v___x_636_);
v___y_587_ = v___x_643_;
goto v___jp_586_;
}
}
v___jp_586_:
{
size_t v_sz_588_; lean_object* v_resultSnap_589_; lean_object* v___x_590_; lean_object* v_cmdState_591_; lean_object* v_infoState_592_; lean_object* v_env_593_; lean_object* v_scopes_594_; lean_object* v_usedQuotCtxts_595_; lean_object* v_nextMacroScope_596_; lean_object* v_maxRecDepth_597_; lean_object* v_ngen_598_; lean_object* v_auxDeclNGen_599_; lean_object* v_traceState_600_; lean_object* v_snapshotTasks_601_; lean_object* v_prevLinterStates_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_629_; 
v_sz_588_ = lean_array_size(v_commands_581_);
v_resultSnap_589_ = lean_ctor_get(v_elabSnap_579_, 2);
lean_inc_ref(v_resultSnap_589_);
lean_dec_ref(v_elabSnap_579_);
v___x_590_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_589_);
v_cmdState_591_ = lean_ctor_get(v___x_590_, 1);
lean_inc_ref(v_cmdState_591_);
lean_dec(v___x_590_);
v_infoState_592_ = lean_ctor_get(v_cmdState_591_, 8);
v_env_593_ = lean_ctor_get(v_cmdState_591_, 0);
v_scopes_594_ = lean_ctor_get(v_cmdState_591_, 2);
v_usedQuotCtxts_595_ = lean_ctor_get(v_cmdState_591_, 3);
v_nextMacroScope_596_ = lean_ctor_get(v_cmdState_591_, 4);
v_maxRecDepth_597_ = lean_ctor_get(v_cmdState_591_, 5);
v_ngen_598_ = lean_ctor_get(v_cmdState_591_, 6);
v_auxDeclNGen_599_ = lean_ctor_get(v_cmdState_591_, 7);
v_traceState_600_ = lean_ctor_get(v_cmdState_591_, 9);
v_snapshotTasks_601_ = lean_ctor_get(v_cmdState_591_, 10);
v_prevLinterStates_602_ = lean_ctor_get(v_cmdState_591_, 11);
v_isSharedCheck_629_ = !lean_is_exclusive(v_cmdState_591_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_cmdState_591_, 1);
lean_dec(v_unused_630_);
v___x_604_ = v_cmdState_591_;
v_isShared_605_ = v_isSharedCheck_629_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_prevLinterStates_602_);
lean_inc(v_snapshotTasks_601_);
lean_inc(v_traceState_600_);
lean_inc(v_infoState_592_);
lean_inc(v_auxDeclNGen_599_);
lean_inc(v_ngen_598_);
lean_inc(v_maxRecDepth_597_);
lean_inc(v_nextMacroScope_596_);
lean_inc(v_usedQuotCtxts_595_);
lean_inc(v_scopes_594_);
lean_inc(v_env_593_);
lean_dec(v_cmdState_591_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_629_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
uint8_t v_enabled_606_; lean_object* v_assignment_607_; lean_object* v_lazyAssignment_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_627_; 
v_enabled_606_ = lean_ctor_get_uint8(v_infoState_592_, sizeof(void*)*3);
v_assignment_607_ = lean_ctor_get(v_infoState_592_, 0);
v_lazyAssignment_608_ = lean_ctor_get(v_infoState_592_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_infoState_592_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_infoState_592_, 2);
lean_dec(v_unused_628_);
v___x_610_ = v_infoState_592_;
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_lazyAssignment_608_);
lean_inc(v_assignment_607_);
lean_dec(v_infoState_592_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_627_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_pos_612_; size_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_trees_617_; lean_object* v___x_619_; 
v_pos_612_ = lean_ctor_get(v_parserState_578_, 0);
lean_inc(v_pos_612_);
v___x_613_ = ((size_t)0ULL);
lean_inc_ref(v_commands_581_);
v___x_614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_588_, v___x_613_, v_commands_581_);
v___x_615_ = lean_array_get_size(v___x_614_);
v___x_616_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_614_, v___x_585_, v___x_615_);
lean_dec_ref(v___x_614_);
v_trees_617_ = l_Lean_Array_toPArray_x27___redArg(v___x_616_);
lean_dec_ref(v___x_616_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 2, v_trees_617_);
v___x_619_ = v___x_610_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_assignment_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_lazyAssignment_608_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_trees_617_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*3, v_enabled_606_);
v___x_619_ = v_reuseFailAlloc_626_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 8, v___x_619_);
lean_ctor_set(v___x_604_, 1, v___y_587_);
v___x_621_ = v___x_604_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_env_593_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___y_587_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_scopes_594_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v_usedQuotCtxts_595_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_nextMacroScope_596_);
lean_ctor_set(v_reuseFailAlloc_625_, 5, v_maxRecDepth_597_);
lean_ctor_set(v_reuseFailAlloc_625_, 6, v_ngen_598_);
lean_ctor_set(v_reuseFailAlloc_625_, 7, v_auxDeclNGen_599_);
lean_ctor_set(v_reuseFailAlloc_625_, 8, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_625_, 9, v_traceState_600_);
lean_ctor_set(v_reuseFailAlloc_625_, 10, v_snapshotTasks_601_);
lean_ctor_set(v_reuseFailAlloc_625_, 11, v_prevLinterStates_602_);
v___x_621_ = v_reuseFailAlloc_625_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_588_, v___x_613_, v_commands_581_);
v___x_623_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v_parserState_578_);
lean_ctor_set(v___x_623_, 2, v_pos_612_);
lean_ctor_set(v___x_623_, 3, v___x_622_);
v___x_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v_inputCtx_572_);
lean_ctor_set(v___x_624_, 2, v_initialSnap_573_);
return v___x_624_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_644_, lean_object* v_initialSnap_645_, lean_object* v_t_646_, lean_object* v_commands_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_644_, v_initialSnap_645_, v_t_646_, v_commands_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_652_, lean_object* v_parserState_653_, lean_object* v_commandState_654_, lean_object* v_old_x3f_655_){
_start:
{
lean_object* v___y_658_; 
if (lean_obj_tag(v_old_x3f_655_) == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_box(0);
v___y_658_ = v___x_663_;
goto v___jp_657_;
}
else
{
lean_object* v_val_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_674_; 
v_val_664_ = lean_ctor_get(v_old_x3f_655_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v_old_x3f_655_);
if (v_isSharedCheck_674_ == 0)
{
v___x_666_ = v_old_x3f_655_;
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_val_664_);
lean_dec(v_old_x3f_655_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_674_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_inputCtx_668_; lean_object* v_initialSnap_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v_inputCtx_668_ = lean_ctor_get(v_val_664_, 1);
lean_inc_ref(v_inputCtx_668_);
v_initialSnap_669_ = lean_ctor_get(v_val_664_, 2);
lean_inc_ref(v_initialSnap_669_);
lean_dec(v_val_664_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_inputCtx_668_);
lean_ctor_set(v___x_670_, 1, v_initialSnap_669_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_670_);
v___x_672_ = v___x_666_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
v___y_658_ = v___x_672_;
goto v___jp_657_;
}
}
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_659_ = l_Lean_Language_Lean_processCommands(v_inputCtx_652_, v_parserState_653_, v_commandState_654_, v___y_658_);
lean_inc_ref(v___x_659_);
v___x_660_ = lean_task_get_own(v___x_659_);
v___x_661_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_662_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_652_, v___x_660_, v___x_659_, v___x_661_);
return v___x_662_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_675_, lean_object* v_parserState_676_, lean_object* v_commandState_677_, lean_object* v_old_x3f_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_675_, v_parserState_676_, v_commandState_677_, v_old_x3f_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_681_, lean_object* v_parserState_682_, lean_object* v_commandState_683_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_toState_687_; lean_object* v___x_688_; 
v___x_685_ = lean_box(0);
v___x_686_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_681_, v_parserState_682_, v_commandState_683_, v___x_685_);
v_toState_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc_ref(v_toState_687_);
lean_dec_ref(v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_toState_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_689_, lean_object* v_parserState_690_, lean_object* v_commandState_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Elab_IO_processCommands(v_inputCtx_689_, v_parserState_690_, v_commandState_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_699_, lean_object* v_env_700_, lean_object* v_opts_701_, lean_object* v_fileName_702_){
_start:
{
lean_object* v___y_705_; 
if (lean_obj_tag(v_fileName_702_) == 0)
{
lean_object* v___x_725_; 
v___x_725_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_705_ = v___x_725_;
goto v___jp_704_;
}
else
{
lean_object* v_val_726_; 
v_val_726_ = lean_ctor_get(v_fileName_702_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v_fileName_702_, 1);
v___y_705_ = v_val_726_;
goto v___jp_704_;
}
v___jp_704_:
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v_inputCtx_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_724_; 
v___x_706_ = 1;
v___x_707_ = lean_string_utf8_byte_size(v_input_699_);
v_inputCtx_708_ = l_Lean_Parser_mkInputContext___redArg(v_input_699_, v___y_705_, v___x_706_, v___x_707_);
v___x_709_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_710_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_711_ = l_Lean_Elab_Command_mkState(v_env_700_, v___x_710_, v_opts_701_);
v___x_712_ = l_Lean_Elab_IO_processCommands(v_inputCtx_708_, v___x_709_, v___x_711_);
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_724_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_commandState_717_; lean_object* v_env_718_; lean_object* v_messages_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v_commandState_717_ = lean_ctor_get(v_a_713_, 0);
lean_inc_ref(v_commandState_717_);
lean_dec(v_a_713_);
v_env_718_ = lean_ctor_get(v_commandState_717_, 0);
lean_inc_ref(v_env_718_);
v_messages_719_ = lean_ctor_get(v_commandState_717_, 1);
lean_inc_ref(v_messages_719_);
lean_dec_ref(v_commandState_717_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v_env_718_);
lean_ctor_set(v___x_720_, 1, v_messages_719_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_720_);
v___x_722_ = v___x_715_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_727_, lean_object* v_env_728_, lean_object* v_opts_729_, lean_object* v_fileName_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Elab_process(v_input_727_, v_env_728_, v_opts_729_, v_fileName_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_733_, lean_object* v_cmdStx_x3f_734_, lean_object* v_acc_735_){
_start:
{
lean_object* v_element_736_; lean_object* v_diagnostics_737_; lean_object* v_children_738_; lean_object* v_msgLog_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_757_; 
v_element_736_ = lean_ctor_get(v_t_733_, 0);
v_diagnostics_737_ = lean_ctor_get(v_element_736_, 1);
lean_inc_ref(v_diagnostics_737_);
v_children_738_ = lean_ctor_get(v_t_733_, 1);
lean_inc_ref(v_children_738_);
lean_dec_ref(v_t_733_);
v_msgLog_739_ = lean_ctor_get(v_diagnostics_737_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_diagnostics_737_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v_diagnostics_737_, 1);
lean_dec(v_unused_758_);
v___x_741_ = v_diagnostics_737_;
v_isShared_742_ = v_isSharedCheck_757_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_msgLog_739_);
lean_dec(v_diagnostics_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_757_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
lean_inc(v_cmdStx_x3f_734_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v_msgLog_739_);
lean_ctor_set(v___x_741_, 0, v_cmdStx_x3f_734_);
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_cmdStx_x3f_734_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_msgLog_739_);
v___x_744_ = v_reuseFailAlloc_756_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v_acc_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_acc_745_ = lean_array_push(v_acc_735_, v___x_744_);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_array_get_size(v_children_738_);
v___x_748_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_dec_ref(v_children_738_);
lean_dec(v_cmdStx_x3f_734_);
return v_acc_745_;
}
else
{
uint8_t v___x_749_; 
v___x_749_ = lean_nat_dec_le(v___x_747_, v___x_747_);
if (v___x_749_ == 0)
{
if (v___x_748_ == 0)
{
lean_dec_ref(v_children_738_);
lean_dec(v_cmdStx_x3f_734_);
return v_acc_745_;
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((size_t)0ULL);
v___x_751_ = lean_usize_of_nat(v___x_747_);
v___x_752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_734_, v_children_738_, v___x_750_, v___x_751_, v_acc_745_);
lean_dec_ref(v_children_738_);
return v___x_752_;
}
}
else
{
size_t v___x_753_; size_t v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((size_t)0ULL);
v___x_754_ = lean_usize_of_nat(v___x_747_);
v___x_755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_734_, v_children_738_, v___x_753_, v___x_754_, v_acc_745_);
lean_dec_ref(v_children_738_);
return v___x_755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_759_, lean_object* v_as_760_, size_t v_i_761_, size_t v_stop_762_, lean_object* v_b_763_){
_start:
{
lean_object* v___y_765_; uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_eq(v_i_761_, v_stop_762_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; lean_object* v_stx_x3f_771_; lean_object* v___x_772_; 
v___x_770_ = lean_array_uget_borrowed(v_as_760_, v_i_761_);
v_stx_x3f_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v___x_770_);
v___x_772_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_770_);
if (lean_obj_tag(v_stx_x3f_771_) == 0)
{
lean_object* v___x_773_; 
lean_inc(v_cmdStx_x3f_759_);
v___x_773_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_772_, v_cmdStx_x3f_759_, v_b_763_);
v___y_765_ = v___x_773_;
goto v___jp_764_;
}
else
{
lean_object* v___x_774_; 
lean_inc_ref(v_stx_x3f_771_);
v___x_774_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_772_, v_stx_x3f_771_, v_b_763_);
v___y_765_ = v___x_774_;
goto v___jp_764_;
}
}
else
{
lean_dec(v_cmdStx_x3f_759_);
return v_b_763_;
}
v___jp_764_:
{
size_t v___x_766_; size_t v___x_767_; 
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_761_, v___x_766_);
v_i_761_ = v___x_767_;
v_b_763_ = v___y_765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_775_, lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_stop_778_, lean_object* v_b_779_){
_start:
{
size_t v_i_boxed_780_; size_t v_stop_boxed_781_; lean_object* v_res_782_; 
v_i_boxed_780_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_stop_boxed_781_ = lean_unbox_usize(v_stop_778_);
lean_dec(v_stop_778_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_775_, v_as_776_, v_i_boxed_780_, v_stop_boxed_781_, v_b_779_);
lean_dec_ref(v_as_776_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5_spec__9(lean_object* v_msg_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_785_ = lean_panic_fn_borrowed(v___x_784_, v_msg_783_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_m_786_, lean_object* v_query_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_zero_791_; uint8_t v_isZero_792_; 
v_zero_791_ = lean_unsigned_to_nat(0u);
v_isZero_792_ = lean_nat_dec_eq(v_x_789_, v_zero_791_);
if (v_isZero_792_ == 1)
{
lean_dec(v_x_790_);
lean_dec(v_x_789_);
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v___x_793_; 
v___x_793_ = lean_box(2);
return v___x_793_;
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_val_794_ = lean_ctor_get(v_x_788_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v_x_788_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v_x_788_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_val_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_keyArray_802_; lean_object* v_valueArray_803_; lean_object* v___x_804_; uint8_t v_isSome_805_; 
v_keyArray_802_ = lean_ctor_get(v_m_786_, 1);
v_valueArray_803_ = lean_ctor_get(v_m_786_, 2);
v___x_804_ = lean_array_fget_borrowed(v_keyArray_802_, v_x_790_);
v_isSome_805_ = lean_noption_is_some(v___x_804_);
if (v_isSome_805_ == 0)
{
lean_dec(v_x_789_);
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_x_790_);
return v___x_806_;
}
else
{
lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_x_790_);
v_val_807_ = lean_ctor_get(v_x_788_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_788_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v_x_788_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_dec(v_x_788_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_val_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_one_815_; lean_object* v_n_816_; lean_object* v___y_818_; 
v_one_815_ = lean_unsigned_to_nat(1u);
v_n_816_ = lean_nat_sub(v_x_789_, v_one_815_);
lean_dec(v_x_789_);
if (v_isSome_805_ == 0)
{
goto v___jp_824_;
}
else
{
lean_object* v___x_826_; uint8_t v_isSome_827_; 
v___x_826_ = lean_array_fget_borrowed(v_valueArray_803_, v_x_790_);
v_isSome_827_ = lean_noption_is_some(v___x_826_);
if (v_isSome_827_ == 0)
{
goto v___jp_824_;
}
else
{
lean_object* v_val_828_; uint8_t v___x_829_; 
lean_inc(v___x_804_);
v_val_828_ = lean_noption_get(v___x_804_);
v___x_829_ = lean_string_dec_eq(v_val_828_, v_query_787_);
if (v___x_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
lean_dec(v_val_828_);
v___x_830_ = lean_array_get_size(v_keyArray_802_);
v___x_831_ = lean_nat_add(v_x_790_, v_one_815_);
lean_dec(v_x_790_);
v___x_832_ = lean_nat_dec_lt(v___x_831_, v___x_830_);
if (v___x_832_ == 0)
{
lean_dec(v___x_831_);
v_x_789_ = v_n_816_;
v_x_790_ = v_zero_791_;
goto _start;
}
else
{
v_x_789_ = v_n_816_;
v_x_790_ = v___x_831_;
goto _start;
}
}
else
{
lean_object* v_val_835_; lean_object* v___x_836_; 
lean_dec(v_n_816_);
lean_dec(v_x_788_);
lean_inc(v___x_826_);
v_val_835_ = lean_noption_get(v___x_826_);
v___x_836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_836_, 0, v_x_790_);
lean_ctor_set(v___x_836_, 1, v_val_828_);
lean_ctor_set(v___x_836_, 2, v_val_835_);
return v___x_836_;
}
}
}
v___jp_817_:
{
lean_object* v___x_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v___x_819_ = lean_array_get_size(v_keyArray_802_);
v___x_820_ = lean_nat_add(v_x_790_, v_one_815_);
lean_dec(v_x_790_);
v___x_821_ = lean_nat_dec_lt(v___x_820_, v___x_819_);
if (v___x_821_ == 0)
{
lean_dec(v___x_820_);
v_x_788_ = v___y_818_;
v_x_789_ = v_n_816_;
v_x_790_ = v_zero_791_;
goto _start;
}
else
{
v_x_788_ = v___y_818_;
v_x_789_ = v_n_816_;
v_x_790_ = v___x_820_;
goto _start;
}
}
v___jp_824_:
{
if (lean_obj_tag(v_x_788_) == 0)
{
lean_object* v___x_825_; 
lean_inc(v_x_790_);
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v_x_790_);
v___y_818_ = v___x_825_;
goto v___jp_817_;
}
else
{
v___y_818_ = v_x_788_;
goto v___jp_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_m_837_, lean_object* v_query_838_, lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_m_837_, v_query_838_, v_x_839_, v_x_840_, v_x_841_);
lean_dec_ref(v_query_838_);
lean_dec_ref(v_m_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_843_, lean_object* v_query_844_){
_start:
{
lean_object* v_keyArray_845_; lean_object* v___x_846_; uint64_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v_fold_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; size_t v___x_857_; size_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_keyArray_845_ = lean_ctor_get(v_m_843_, 1);
v___x_846_ = lean_array_get_size(v_keyArray_845_);
v___x_847_ = lean_string_hash(v_query_844_);
v___x_848_ = 32ULL;
v___x_849_ = lean_uint64_shift_right(v___x_847_, v___x_848_);
v_fold_850_ = lean_uint64_xor(v___x_847_, v___x_849_);
v___x_851_ = 16ULL;
v___x_852_ = lean_uint64_shift_right(v_fold_850_, v___x_851_);
v___x_853_ = lean_uint64_xor(v_fold_850_, v___x_852_);
v___x_854_ = lean_uint64_to_usize(v___x_853_);
v___x_855_ = lean_usize_of_nat(v___x_846_);
v___x_856_ = ((size_t)1ULL);
v___x_857_ = lean_usize_sub(v___x_855_, v___x_856_);
v___x_858_ = lean_usize_land(v___x_854_, v___x_857_);
v___x_859_ = lean_usize_to_nat(v___x_858_);
v___x_860_ = lean_box(0);
v___x_861_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_m_843_, v_query_844_, v___x_860_, v___x_846_, v___x_859_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg___boxed(lean_object* v_m_862_, lean_object* v_query_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_862_, v_query_863_);
lean_dec_ref(v_query_863_);
lean_dec_ref(v_m_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg(lean_object* v_m_865_, lean_object* v_query_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_865_, v_query_866_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_index_868_; lean_object* v_key_869_; lean_object* v_value_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_index_868_ = lean_ctor_get(v___x_867_, 0);
v_key_869_ = lean_ctor_get(v___x_867_, 1);
v_value_870_ = lean_ctor_get(v___x_867_, 2);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_867_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_value_870_);
lean_inc(v_key_869_);
lean_inc(v_index_868_);
lean_dec(v___x_867_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_index_868_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_key_869_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v_value_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v___x_867_);
v___x_878_ = lean_box(1);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg___boxed(lean_object* v_m_879_, lean_object* v_query_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg(v_m_879_, v_query_880_);
lean_dec_ref(v_query_880_);
lean_dec_ref(v_m_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_m_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg(v_m_882_, v_a_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_value_885_; lean_object* v___x_886_; 
v_value_885_ = lean_ctor_get(v___x_884_, 2);
lean_inc(v_value_885_);
lean_dec_ref_known(v___x_884_, 3);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v_value_885_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_box(0);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_m_888_, v_a_889_);
lean_dec_ref(v_a_889_);
lean_dec_ref(v_m_888_);
return v_res_890_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__3(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_894_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__2));
v___x_895_ = lean_unsigned_to_nat(12u);
v___x_896_ = lean_unsigned_to_nat(672u);
v___x_897_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__1));
v___x_898_ = ((lean_object*)(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__0));
v___x_899_ = l_mkPanicMessageWithDecl(v___x_898_, v___x_897_, v___x_896_, v___x_895_, v___x_894_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v_m_900_, lean_object* v_a_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_m_900_, v_a_901_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__3, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__3_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___closed__3);
v___x_904_ = l_panic___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5_spec__9(v___x_903_);
return v___x_904_;
}
else
{
lean_object* v_val_905_; 
v_val_905_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_val_905_);
lean_dec_ref_known(v___x_902_, 1);
return v_val_905_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v_m_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_m_906_, v_a_907_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_m_906_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__6(lean_object* v___x_909_, size_t v_sz_910_, size_t v_i_911_, lean_object* v_bs_912_){
_start:
{
uint8_t v___x_913_; 
v___x_913_ = lean_usize_dec_lt(v_i_911_, v_sz_910_);
if (v___x_913_ == 0)
{
return v_bs_912_;
}
else
{
lean_object* v_v_914_; lean_object* v___x_915_; lean_object* v_bs_x27_916_; lean_object* v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v_v_914_ = lean_array_uget(v_bs_912_, v_i_911_);
v___x_915_ = lean_unsigned_to_nat(0u);
v_bs_x27_916_ = lean_array_uset(v_bs_912_, v_i_911_, v___x_915_);
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_909_, v_v_914_);
lean_dec(v_v_914_);
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_911_, v___x_918_);
v___x_920_ = lean_array_uset(v_bs_x27_916_, v_i_911_, v___x_917_);
v_i_911_ = v___x_919_;
v_bs_912_ = v___x_920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__6___boxed(lean_object* v___x_922_, lean_object* v_sz_923_, lean_object* v_i_924_, lean_object* v_bs_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_923_);
lean_dec(v_sz_923_);
v_i_boxed_927_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__6(v___x_922_, v_sz_boxed_926_, v_i_boxed_927_, v_bs_925_);
lean_dec_ref(v___x_922_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__4(lean_object* v_filePath_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_lean_x3f_931_; lean_object* v_olean_x3f_932_; lean_object* v_oleanPrivate_x3f_933_; lean_object* v_ilean_x3f_934_; lean_object* v_irSig_x3f_935_; lean_object* v_ir_x3f_936_; lean_object* v_c_x3f_937_; lean_object* v_bc_x3f_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
v_lean_x3f_931_ = lean_ctor_get(v_a_930_, 0);
v_olean_x3f_932_ = lean_ctor_get(v_a_930_, 1);
v_oleanPrivate_x3f_933_ = lean_ctor_get(v_a_930_, 3);
v_ilean_x3f_934_ = lean_ctor_get(v_a_930_, 4);
v_irSig_x3f_935_ = lean_ctor_get(v_a_930_, 5);
v_ir_x3f_936_ = lean_ctor_get(v_a_930_, 6);
v_c_x3f_937_ = lean_ctor_get(v_a_930_, 7);
v_bc_x3f_938_ = lean_ctor_get(v_a_930_, 8);
v_isSharedCheck_946_ = !lean_is_exclusive(v_a_930_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v_a_930_, 2);
lean_dec(v_unused_947_);
v___x_940_ = v_a_930_;
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_bc_x3f_938_);
lean_inc(v_c_x3f_937_);
lean_inc(v_ir_x3f_936_);
lean_inc(v_irSig_x3f_935_);
lean_inc(v_ilean_x3f_934_);
lean_inc(v_oleanPrivate_x3f_933_);
lean_inc(v_olean_x3f_932_);
lean_inc(v_lean_x3f_931_);
lean_dec(v_a_930_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_946_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_filePath_929_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 2, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_lean_x3f_931_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_olean_x3f_932_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_oleanPrivate_x3f_933_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_ilean_x3f_934_);
lean_ctor_set(v_reuseFailAlloc_945_, 5, v_irSig_x3f_935_);
lean_ctor_set(v_reuseFailAlloc_945_, 6, v_ir_x3f_936_);
lean_ctor_set(v_reuseFailAlloc_945_, 7, v_c_x3f_937_);
lean_ctor_set(v_reuseFailAlloc_945_, 8, v_bc_x3f_938_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__2(lean_object* v_filePath_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_lean_x3f_950_; lean_object* v_olean_x3f_951_; lean_object* v_oleanServer_x3f_952_; lean_object* v_oleanPrivate_x3f_953_; lean_object* v_ilean_x3f_954_; lean_object* v_irSig_x3f_955_; lean_object* v_c_x3f_956_; lean_object* v_bc_x3f_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_965_; 
v_lean_x3f_950_ = lean_ctor_get(v_a_949_, 0);
v_olean_x3f_951_ = lean_ctor_get(v_a_949_, 1);
v_oleanServer_x3f_952_ = lean_ctor_get(v_a_949_, 2);
v_oleanPrivate_x3f_953_ = lean_ctor_get(v_a_949_, 3);
v_ilean_x3f_954_ = lean_ctor_get(v_a_949_, 4);
v_irSig_x3f_955_ = lean_ctor_get(v_a_949_, 5);
v_c_x3f_956_ = lean_ctor_get(v_a_949_, 7);
v_bc_x3f_957_ = lean_ctor_get(v_a_949_, 8);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_949_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_a_949_, 6);
lean_dec(v_unused_966_);
v___x_959_ = v_a_949_;
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_bc_x3f_957_);
lean_inc(v_c_x3f_956_);
lean_inc(v_irSig_x3f_955_);
lean_inc(v_ilean_x3f_954_);
lean_inc(v_oleanPrivate_x3f_953_);
lean_inc(v_oleanServer_x3f_952_);
lean_inc(v_olean_x3f_951_);
lean_inc(v_lean_x3f_950_);
lean_dec(v_a_949_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_965_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v_filePath_948_);
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 6, v___x_961_);
v___x_963_ = v___x_959_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_lean_x3f_950_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_olean_x3f_951_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_oleanServer_x3f_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_oleanPrivate_x3f_953_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v_ilean_x3f_954_);
lean_ctor_set(v_reuseFailAlloc_964_, 5, v_irSig_x3f_955_);
lean_ctor_set(v_reuseFailAlloc_964_, 6, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_964_, 7, v_c_x3f_956_);
lean_ctor_set(v_reuseFailAlloc_964_, 8, v_bc_x3f_957_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_967_, lean_object* v_a_968_, lean_object* v_fallback_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_m_967_, v_a_968_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_inc(v_fallback_969_);
return v_fallback_969_;
}
else
{
lean_object* v_val_971_; 
v_val_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_val_971_);
lean_dec_ref_known(v___x_970_, 1);
return v_val_971_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_972_, lean_object* v_a_973_, lean_object* v_fallback_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_972_, v_a_973_, v_fallback_974_);
lean_dec(v_fallback_974_);
lean_dec_ref(v_a_973_);
lean_dec_ref(v_m_972_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___redArg(lean_object* v_b_976_, lean_object* v_acc_977_, lean_object* v_i_978_){
_start:
{
lean_object* v___y_980_; lean_object* v_keyArray_988_; lean_object* v_valueArray_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_keyArray_988_ = lean_ctor_get(v_b_976_, 1);
v_valueArray_989_ = lean_ctor_get(v_b_976_, 2);
v___x_990_ = lean_array_get_size(v_keyArray_988_);
v___x_991_ = lean_nat_dec_lt(v_i_978_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec(v_i_978_);
return v_acc_977_;
}
else
{
lean_object* v___x_992_; uint8_t v_isSome_993_; 
v___x_992_ = lean_array_fget_borrowed(v_keyArray_988_, v_i_978_);
v_isSome_993_ = lean_noption_is_some(v___x_992_);
if (v_isSome_993_ == 0)
{
goto v___jp_984_;
}
else
{
lean_object* v___x_994_; uint8_t v_isSome_995_; 
v___x_994_ = lean_array_fget_borrowed(v_valueArray_989_, v_i_978_);
v_isSome_995_ = lean_noption_is_some(v___x_994_);
if (v_isSome_995_ == 0)
{
goto v___jp_984_;
}
else
{
lean_object* v_val_996_; lean_object* v_val_997_; lean_object* v_i_999_; lean_object* v___x_1004_; 
lean_inc(v___x_992_);
v_val_996_ = lean_noption_get(v___x_992_);
lean_inc(v___x_994_);
v_val_997_ = lean_noption_get(v___x_994_);
v___x_1004_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_acc_977_, v_val_996_);
switch(lean_obj_tag(v___x_1004_))
{
case 0:
{
lean_object* v_index_1005_; lean_object* v_size_1006_; lean_object* v___x_1007_; 
v_index_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_index_1005_);
lean_dec_ref_known(v___x_1004_, 3);
v_size_1006_ = lean_ctor_get(v_acc_977_, 0);
lean_inc(v_size_1006_);
v___x_1007_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_977_, v_size_1006_, v_index_1005_, v_val_996_, v_val_997_);
lean_dec(v_index_1005_);
v___y_980_ = v___x_1007_;
goto v___jp_979_;
}
case 1:
{
lean_object* v_index_1008_; 
v_index_1008_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_index_1008_);
lean_dec_ref_known(v___x_1004_, 1);
v_i_999_ = v_index_1008_;
goto v___jp_998_;
}
default: 
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_977_, v___x_1009_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_index_1011_; 
v_index_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_index_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v_i_999_ = v_index_1011_;
goto v___jp_998_;
}
else
{
lean_dec(v_val_997_);
lean_dec(v_val_996_);
v___y_980_ = v_acc_977_;
goto v___jp_979_;
}
}
}
v___jp_998_:
{
lean_object* v_size_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_size_1000_ = lean_ctor_get(v_acc_977_, 0);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_size_1000_, v___x_1001_);
v___x_1003_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_977_, v___x_1002_, v_i_999_, v_val_996_, v_val_997_);
lean_dec(v_i_999_);
v___y_980_ = v___x_1003_;
goto v___jp_979_;
}
}
}
}
v___jp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_add(v_i_978_, v___x_981_);
lean_dec(v_i_978_);
v_acc_977_ = v___y_980_;
v_i_978_ = v___x_982_;
goto _start;
}
v___jp_984_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_unsigned_to_nat(1u);
v___x_986_ = lean_nat_add(v_i_978_, v___x_985_);
lean_dec(v_i_978_);
v_i_978_ = v___x_986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_1012_, lean_object* v_acc_1013_, lean_object* v_i_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___redArg(v_b_1012_, v_acc_1013_, v_i_1014_);
lean_dec_ref(v_b_1012_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___redArg(lean_object* v_init_1016_, lean_object* v_b_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___redArg(v_b_1017_, v_init_1016_, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___redArg___boxed(lean_object* v_init_1020_, lean_object* v_b_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___redArg(v_init_1020_, v_b_1021_);
lean_dec_ref(v_b_1021_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_1023_){
_start:
{
lean_object* v_keyArray_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_cellCount_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_target_1031_; lean_object* v___x_1032_; 
v_keyArray_1024_ = lean_ctor_get(v_m_1023_, 1);
v___x_1025_ = lean_array_get_size(v_keyArray_1024_);
v___x_1026_ = lean_unsigned_to_nat(2u);
v_cellCount_1027_ = lean_nat_mul(v___x_1025_, v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_1027_);
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1027_);
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1027_);
v_target_1031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_1031_, 0, v___x_1028_);
lean_ctor_set(v_target_1031_, 1, v___x_1029_);
lean_ctor_set(v_target_1031_, 2, v___x_1030_);
v___x_1032_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___redArg(v_target_1031_, v_m_1023_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1033_);
lean_dec_ref(v_m_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__0(lean_object* v_filePath_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_lean_x3f_1037_; lean_object* v_oleanServer_x3f_1038_; lean_object* v_oleanPrivate_x3f_1039_; lean_object* v_ilean_x3f_1040_; lean_object* v_irSig_x3f_1041_; lean_object* v_ir_x3f_1042_; lean_object* v_c_x3f_1043_; lean_object* v_bc_x3f_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1052_; 
v_lean_x3f_1037_ = lean_ctor_get(v_a_1036_, 0);
v_oleanServer_x3f_1038_ = lean_ctor_get(v_a_1036_, 2);
v_oleanPrivate_x3f_1039_ = lean_ctor_get(v_a_1036_, 3);
v_ilean_x3f_1040_ = lean_ctor_get(v_a_1036_, 4);
v_irSig_x3f_1041_ = lean_ctor_get(v_a_1036_, 5);
v_ir_x3f_1042_ = lean_ctor_get(v_a_1036_, 6);
v_c_x3f_1043_ = lean_ctor_get(v_a_1036_, 7);
v_bc_x3f_1044_ = lean_ctor_get(v_a_1036_, 8);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_a_1036_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_a_1036_, 1);
lean_dec(v_unused_1053_);
v___x_1046_ = v_a_1036_;
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_bc_x3f_1044_);
lean_inc(v_c_x3f_1043_);
lean_inc(v_ir_x3f_1042_);
lean_inc(v_irSig_x3f_1041_);
lean_inc(v_ilean_x3f_1040_);
lean_inc(v_oleanPrivate_x3f_1039_);
lean_inc(v_oleanServer_x3f_1038_);
lean_inc(v_lean_x3f_1037_);
lean_dec(v_a_1036_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1052_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_filePath_1035_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1048_);
v___x_1050_ = v___x_1046_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_lean_x3f_1037_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_oleanServer_x3f_1038_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_oleanPrivate_x3f_1039_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_ilean_x3f_1040_);
lean_ctor_set(v_reuseFailAlloc_1051_, 5, v_irSig_x3f_1041_);
lean_ctor_set(v_reuseFailAlloc_1051_, 6, v_ir_x3f_1042_);
lean_ctor_set(v_reuseFailAlloc_1051_, 7, v_c_x3f_1043_);
lean_ctor_set(v_reuseFailAlloc_1051_, 8, v_bc_x3f_1044_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__3(lean_object* v_filePath_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_lean_x3f_1056_; lean_object* v_olean_x3f_1057_; lean_object* v_oleanServer_x3f_1058_; lean_object* v_ilean_x3f_1059_; lean_object* v_irSig_x3f_1060_; lean_object* v_ir_x3f_1061_; lean_object* v_c_x3f_1062_; lean_object* v_bc_x3f_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1071_; 
v_lean_x3f_1056_ = lean_ctor_get(v_a_1055_, 0);
v_olean_x3f_1057_ = lean_ctor_get(v_a_1055_, 1);
v_oleanServer_x3f_1058_ = lean_ctor_get(v_a_1055_, 2);
v_ilean_x3f_1059_ = lean_ctor_get(v_a_1055_, 4);
v_irSig_x3f_1060_ = lean_ctor_get(v_a_1055_, 5);
v_ir_x3f_1061_ = lean_ctor_get(v_a_1055_, 6);
v_c_x3f_1062_ = lean_ctor_get(v_a_1055_, 7);
v_bc_x3f_1063_ = lean_ctor_get(v_a_1055_, 8);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_a_1055_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_a_1055_, 3);
lean_dec(v_unused_1072_);
v___x_1065_ = v_a_1055_;
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_bc_x3f_1063_);
lean_inc(v_c_x3f_1062_);
lean_inc(v_ir_x3f_1061_);
lean_inc(v_irSig_x3f_1060_);
lean_inc(v_ilean_x3f_1059_);
lean_inc(v_oleanServer_x3f_1058_);
lean_inc(v_olean_x3f_1057_);
lean_inc(v_lean_x3f_1056_);
lean_dec(v_a_1055_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1071_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v_filePath_1054_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 3, v___x_1067_);
v___x_1069_ = v___x_1065_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_lean_x3f_1056_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_olean_x3f_1057_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_oleanServer_x3f_1058_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_ilean_x3f_1059_);
lean_ctor_set(v_reuseFailAlloc_1070_, 5, v_irSig_x3f_1060_);
lean_ctor_set(v_reuseFailAlloc_1070_, 6, v_ir_x3f_1061_);
lean_ctor_set(v_reuseFailAlloc_1070_, 7, v_c_x3f_1062_);
lean_ctor_set(v_reuseFailAlloc_1070_, 8, v_bc_x3f_1063_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__1(lean_object* v_filePath_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_lean_x3f_1075_; lean_object* v_olean_x3f_1076_; lean_object* v_oleanServer_x3f_1077_; lean_object* v_oleanPrivate_x3f_1078_; lean_object* v_ilean_x3f_1079_; lean_object* v_ir_x3f_1080_; lean_object* v_c_x3f_1081_; lean_object* v_bc_x3f_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1090_; 
v_lean_x3f_1075_ = lean_ctor_get(v_a_1074_, 0);
v_olean_x3f_1076_ = lean_ctor_get(v_a_1074_, 1);
v_oleanServer_x3f_1077_ = lean_ctor_get(v_a_1074_, 2);
v_oleanPrivate_x3f_1078_ = lean_ctor_get(v_a_1074_, 3);
v_ilean_x3f_1079_ = lean_ctor_get(v_a_1074_, 4);
v_ir_x3f_1080_ = lean_ctor_get(v_a_1074_, 6);
v_c_x3f_1081_ = lean_ctor_get(v_a_1074_, 7);
v_bc_x3f_1082_ = lean_ctor_get(v_a_1074_, 8);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_a_1074_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_a_1074_, 5);
lean_dec(v_unused_1091_);
v___x_1084_ = v_a_1074_;
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_bc_x3f_1082_);
lean_inc(v_c_x3f_1081_);
lean_inc(v_ir_x3f_1080_);
lean_inc(v_ilean_x3f_1079_);
lean_inc(v_oleanPrivate_x3f_1078_);
lean_inc(v_oleanServer_x3f_1077_);
lean_inc(v_olean_x3f_1076_);
lean_inc(v_lean_x3f_1075_);
lean_dec(v_a_1074_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1090_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_filePath_1073_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 5, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_lean_x3f_1075_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_olean_x3f_1076_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_oleanServer_x3f_1077_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_oleanPrivate_x3f_1078_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_ilean_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 6, v_ir_x3f_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 7, v_c_x3f_1081_);
lean_ctor_set(v_reuseFailAlloc_1089_, 8, v_bc_x3f_1082_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___redArg(lean_object* v_m_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg(v_m_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
uint8_t v___x_1095_; 
lean_dec_ref_known(v___x_1094_, 3);
v___x_1095_ = 1;
return v___x_1095_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = 0;
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___redArg___boxed(lean_object* v_m_1097_, lean_object* v_a_1098_){
_start:
{
uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_res_1099_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___redArg(v_m_1097_, v_a_1098_);
lean_dec_ref(v_a_1098_);
lean_dec_ref(v_m_1097_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_as_1109_, size_t v_sz_1110_, size_t v_i_1111_, lean_object* v_b_1112_){
_start:
{
lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v_i_1125_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v_i_1135_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; uint8_t v___x_1153_; 
v___x_1153_ = lean_usize_dec_lt(v_i_1111_, v_sz_1110_);
if (v___x_1153_ == 0)
{
return v_b_1112_;
}
else
{
lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v_order_1172_; lean_object* v_fst_1207_; lean_object* v_snd_1208_; lean_object* v_a_1211_; lean_object* v_filePath_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; 
v_fst_1154_ = lean_ctor_get(v_b_1112_, 0);
lean_inc(v_fst_1154_);
v_snd_1155_ = lean_ctor_get(v_b_1112_, 1);
lean_inc(v_snd_1155_);
lean_dec_ref(v_b_1112_);
v_a_1211_ = lean_array_uget_borrowed(v_as_1109_, v_i_1111_);
v_filePath_1212_ = lean_ctor_get(v_a_1211_, 0);
lean_inc_ref_n(v_filePath_1212_, 2);
v___f_1213_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_1213_, 0, v_filePath_1212_);
v___x_1214_ = l_System_FilePath_extension(v_filePath_1212_);
if (lean_obj_tag(v___x_1214_) == 1)
{
lean_object* v_val_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__1));
v___x_1217_ = lean_string_dec_eq(v_val_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__2));
v___x_1219_ = lean_string_dec_eq(v_val_1215_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__3));
v___x_1221_ = lean_string_dec_eq(v_val_1215_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__4));
v___x_1223_ = lean_string_dec_eq(v_val_1215_, v___x_1222_);
lean_dec(v_val_1215_);
if (v___x_1223_ == 0)
{
lean_inc_ref(v_filePath_1212_);
v_fst_1207_ = v_filePath_1212_;
v_snd_1208_ = v___f_1213_;
goto v___jp_1206_;
}
else
{
lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_dec_ref(v___f_1213_);
lean_inc_ref_n(v_filePath_1212_, 2);
v___f_1224_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__1), 2, 1);
lean_closure_set(v___f_1224_, 0, v_filePath_1212_);
v___x_1225_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__5));
v___x_1226_ = l_System_FilePath_withExtension(v_filePath_1212_, v___x_1225_);
v___x_1227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__6));
v___x_1228_ = l_System_FilePath_withExtension(v___x_1226_, v___x_1227_);
v_fst_1207_ = v___x_1228_;
v_snd_1208_ = v___f_1224_;
goto v___jp_1206_;
}
}
else
{
lean_object* v___f_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec(v_val_1215_);
lean_dec_ref(v___f_1213_);
lean_inc_ref_n(v_filePath_1212_, 2);
v___f_1229_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__2), 2, 1);
lean_closure_set(v___f_1229_, 0, v_filePath_1212_);
v___x_1230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__6));
v___x_1231_ = l_System_FilePath_withExtension(v_filePath_1212_, v___x_1230_);
v_fst_1207_ = v___x_1231_;
v_snd_1208_ = v___f_1229_;
goto v___jp_1206_;
}
}
else
{
lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec(v_val_1215_);
lean_dec_ref(v___f_1213_);
lean_inc_ref_n(v_filePath_1212_, 2);
v___f_1232_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__3), 2, 1);
lean_closure_set(v___f_1232_, 0, v_filePath_1212_);
v___x_1233_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__5));
v___x_1234_ = l_System_FilePath_withExtension(v_filePath_1212_, v___x_1233_);
v_fst_1207_ = v___x_1234_;
v_snd_1208_ = v___f_1232_;
goto v___jp_1206_;
}
}
else
{
lean_object* v___f_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
lean_dec(v_val_1215_);
lean_dec_ref(v___f_1213_);
lean_inc_ref_n(v_filePath_1212_, 2);
v___f_1235_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___lam__4), 2, 1);
lean_closure_set(v___f_1235_, 0, v_filePath_1212_);
v___x_1236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__5));
v___x_1237_ = l_System_FilePath_withExtension(v_filePath_1212_, v___x_1236_);
v_fst_1207_ = v___x_1237_;
v_snd_1208_ = v___f_1235_;
goto v___jp_1206_;
}
}
else
{
lean_dec(v___x_1214_);
lean_inc_ref(v_filePath_1212_);
v_fst_1207_ = v_filePath_1212_;
v_snd_1208_ = v___f_1213_;
goto v___jp_1206_;
}
v___jp_1156_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1155_);
lean_dec(v_snd_1155_);
v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v___x_1160_, v___y_1158_);
switch(lean_obj_tag(v___x_1161_))
{
case 0:
{
lean_object* v_index_1162_; lean_object* v_size_1163_; lean_object* v___x_1164_; 
v_index_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_index_1162_);
lean_dec_ref_known(v___x_1161_, 3);
v_size_1163_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_size_1163_);
v___x_1164_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1160_, v_size_1163_, v_index_1162_, v___y_1158_, v___y_1159_);
lean_dec(v_index_1162_);
v___y_1114_ = v___y_1157_;
v___y_1115_ = v___x_1164_;
goto v___jp_1113_;
}
case 1:
{
lean_object* v_index_1165_; 
v_index_1165_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_index_1165_);
lean_dec_ref_known(v___x_1161_, 1);
v___y_1121_ = v___y_1157_;
v___y_1122_ = v___x_1160_;
v___y_1123_ = v___y_1158_;
v___y_1124_ = v___y_1159_;
v_i_1125_ = v_index_1165_;
goto v___jp_1120_;
}
default: 
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1160_, v___x_1166_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_index_1168_; 
v_index_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_index_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___y_1121_ = v___y_1157_;
v___y_1122_ = v___x_1160_;
v___y_1123_ = v___y_1158_;
v___y_1124_ = v___y_1159_;
v_i_1125_ = v_index_1168_;
goto v___jp_1120_;
}
else
{
lean_dec_ref(v___y_1159_);
lean_dec_ref(v___y_1158_);
v___y_1114_ = v___y_1157_;
v___y_1115_ = v___x_1160_;
goto v___jp_1113_;
}
}
}
}
v___jp_1169_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___closed__0));
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1155_, v___y_1171_, v___x_1173_);
v___x_1175_ = lean_apply_1(v___y_1170_, v___x_1174_);
v___x_1176_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1155_, v___y_1171_);
switch(lean_obj_tag(v___x_1176_))
{
case 0:
{
lean_object* v_index_1177_; lean_object* v_size_1178_; lean_object* v___x_1179_; 
v_index_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_index_1177_);
lean_dec_ref_known(v___x_1176_, 3);
v_size_1178_ = lean_ctor_get(v_snd_1155_, 0);
lean_inc(v_size_1178_);
v___x_1179_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1155_, v_size_1178_, v_index_1177_, v___y_1171_, v___x_1175_);
lean_dec(v_index_1177_);
v___y_1114_ = v_order_1172_;
v___y_1115_ = v___x_1179_;
goto v___jp_1113_;
}
case 1:
{
lean_object* v_index_1180_; lean_object* v_size_1181_; lean_object* v_keyArray_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_index_1180_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_index_1180_);
lean_dec_ref_known(v___x_1176_, 1);
v_size_1181_ = lean_ctor_get(v_snd_1155_, 0);
v_keyArray_1182_ = lean_ctor_get(v_snd_1155_, 1);
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_nat_add(v_size_1181_, v___x_1183_);
v___x_1185_ = lean_array_get_size(v_keyArray_1182_);
v___x_1186_ = lean_nat_dec_lt(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v___x_1184_);
lean_dec(v_index_1180_);
v___y_1157_ = v_order_1172_;
v___y_1158_ = v___y_1171_;
v___y_1159_ = v___x_1175_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1187_ = lean_unsigned_to_nat(4u);
v___x_1188_ = lean_nat_mul(v___x_1184_, v___x_1187_);
v___x_1189_ = lean_unsigned_to_nat(3u);
v___x_1190_ = lean_nat_mul(v___x_1185_, v___x_1189_);
v___x_1191_ = lean_nat_dec_le(v___x_1188_, v___x_1190_);
lean_dec(v___x_1190_);
lean_dec(v___x_1188_);
if (v___x_1191_ == 0)
{
lean_dec(v___x_1184_);
lean_dec(v_index_1180_);
v___y_1157_ = v_order_1172_;
v___y_1158_ = v___y_1171_;
v___y_1159_ = v___x_1175_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1155_, v___x_1184_, v_index_1180_, v___y_1171_, v___x_1175_);
lean_dec(v_index_1180_);
v___y_1114_ = v_order_1172_;
v___y_1115_ = v___x_1192_;
goto v___jp_1113_;
}
}
}
default: 
{
lean_object* v_size_1193_; lean_object* v_keyArray_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_size_1193_ = lean_ctor_get(v_snd_1155_, 0);
v_keyArray_1194_ = lean_ctor_get(v_snd_1155_, 1);
v___x_1195_ = lean_unsigned_to_nat(1u);
v___x_1196_ = lean_nat_add(v_size_1193_, v___x_1195_);
v___x_1197_ = lean_array_get_size(v_keyArray_1194_);
v___x_1198_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec(v___x_1196_);
v___x_1199_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1155_);
lean_dec(v_snd_1155_);
v___y_1141_ = v_order_1172_;
v___y_1142_ = v___y_1171_;
v___y_1143_ = v___x_1175_;
v___y_1144_ = v___x_1199_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1200_ = lean_unsigned_to_nat(4u);
v___x_1201_ = lean_nat_mul(v___x_1196_, v___x_1200_);
lean_dec(v___x_1196_);
v___x_1202_ = lean_unsigned_to_nat(3u);
v___x_1203_ = lean_nat_mul(v___x_1197_, v___x_1202_);
v___x_1204_ = lean_nat_dec_le(v___x_1201_, v___x_1203_);
lean_dec(v___x_1203_);
lean_dec(v___x_1201_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1155_);
lean_dec(v_snd_1155_);
v___y_1141_ = v_order_1172_;
v___y_1142_ = v___y_1171_;
v___y_1143_ = v___x_1175_;
v___y_1144_ = v___x_1205_;
goto v___jp_1140_;
}
else
{
v___y_1141_ = v_order_1172_;
v___y_1142_ = v___y_1171_;
v___y_1143_ = v___x_1175_;
v___y_1144_ = v_snd_1155_;
goto v___jp_1140_;
}
}
}
}
}
v___jp_1206_:
{
uint8_t v___x_1209_; 
v___x_1209_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___redArg(v_snd_1155_, v_fst_1207_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_inc_ref(v_fst_1207_);
v___x_1210_ = lean_array_push(v_fst_1154_, v_fst_1207_);
v___y_1170_ = v_snd_1208_;
v___y_1171_ = v_fst_1207_;
v_order_1172_ = v___x_1210_;
goto v___jp_1169_;
}
else
{
v___y_1170_ = v_snd_1208_;
v___y_1171_ = v_fst_1207_;
v_order_1172_ = v_fst_1154_;
goto v___jp_1169_;
}
}
}
v___jp_1113_:
{
lean_object* v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; 
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___y_1114_);
lean_ctor_set(v___x_1116_, 1, v___y_1115_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_add(v_i_1111_, v___x_1117_);
v_i_1111_ = v___x_1118_;
v_b_1112_ = v___x_1116_;
goto _start;
}
v___jp_1120_:
{
lean_object* v_size_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_size_1126_ = lean_ctor_get(v___y_1122_, 0);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_size_1126_, v___x_1127_);
v___x_1129_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1122_, v___x_1128_, v_i_1125_, v___y_1123_, v___y_1124_);
lean_dec(v_i_1125_);
v___y_1114_ = v___y_1121_;
v___y_1115_ = v___x_1129_;
goto v___jp_1113_;
}
v___jp_1130_:
{
lean_object* v_size_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_size_1136_ = lean_ctor_get(v___y_1132_, 0);
v___x_1137_ = lean_unsigned_to_nat(1u);
v___x_1138_ = lean_nat_add(v_size_1136_, v___x_1137_);
v___x_1139_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1132_, v___x_1138_, v_i_1135_, v___y_1133_, v___y_1134_);
lean_dec(v_i_1135_);
v___y_1114_ = v___y_1131_;
v___y_1115_ = v___x_1139_;
goto v___jp_1113_;
}
v___jp_1140_:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v___y_1144_, v___y_1142_);
switch(lean_obj_tag(v___x_1145_))
{
case 0:
{
lean_object* v_index_1146_; lean_object* v_size_1147_; lean_object* v___x_1148_; 
v_index_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_index_1146_);
lean_dec_ref_known(v___x_1145_, 3);
v_size_1147_ = lean_ctor_get(v___y_1144_, 0);
lean_inc(v_size_1147_);
v___x_1148_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1144_, v_size_1147_, v_index_1146_, v___y_1142_, v___y_1143_);
lean_dec(v_index_1146_);
v___y_1114_ = v___y_1141_;
v___y_1115_ = v___x_1148_;
goto v___jp_1113_;
}
case 1:
{
lean_object* v_index_1149_; 
v_index_1149_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_index_1149_);
lean_dec_ref_known(v___x_1145_, 1);
v___y_1131_ = v___y_1141_;
v___y_1132_ = v___y_1144_;
v___y_1133_ = v___y_1142_;
v___y_1134_ = v___y_1143_;
v_i_1135_ = v_index_1149_;
goto v___jp_1130_;
}
default: 
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1144_, v___x_1150_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_index_1152_; 
v_index_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_index_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___y_1131_ = v___y_1141_;
v___y_1132_ = v___y_1144_;
v___y_1133_ = v___y_1142_;
v___y_1134_ = v___y_1143_;
v_i_1135_ = v_index_1152_;
goto v___jp_1130_;
}
else
{
lean_dec_ref(v___y_1143_);
lean_dec_ref(v___y_1142_);
v___y_1114_ = v___y_1141_;
v___y_1115_ = v___y_1144_;
goto v___jp_1113_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_as_1238_, lean_object* v_sz_1239_, lean_object* v_i_1240_, lean_object* v_b_1241_){
_start:
{
size_t v_sz_boxed_1242_; size_t v_i_boxed_1243_; lean_object* v_res_1244_; 
v_sz_boxed_1242_ = lean_unbox_usize(v_sz_1239_);
lean_dec(v_sz_1239_);
v_i_boxed_1243_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_res_1244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_as_1238_, v_sz_boxed_1242_, v_i_boxed_1243_, v_b_1241_);
lean_dec_ref(v_as_1238_);
return v_res_1244_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v_cellCount_1247_; lean_object* v___x_1248_; 
v_cellCount_1247_ = lean_unsigned_to_nat(16u);
v___x_1248_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1247_);
return v___x_1248_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v_cellCount_1249_; lean_object* v___x_1250_; 
v_cellCount_1249_ = lean_unsigned_to_nat(16u);
v___x_1250_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_byBase_1254_; 
v___x_1251_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v___x_1252_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1253_ = lean_unsigned_to_nat(0u);
v_byBase_1254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_byBase_1254_, 0, v___x_1253_);
lean_ctor_set(v_byBase_1254_, 1, v___x_1252_);
lean_ctor_set(v_byBase_1254_, 2, v___x_1251_);
return v_byBase_1254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__4(void){
_start:
{
lean_object* v_byBase_1255_; lean_object* v_order_1256_; lean_object* v___x_1257_; 
v_byBase_1255_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_order_1256_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_order_1256_);
lean_ctor_set(v___x_1257_, 1, v_byBase_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1258_){
_start:
{
lean_object* v___x_1259_; size_t v_sz_1260_; size_t v___x_1261_; lean_object* v___x_1262_; lean_object* v_fst_1263_; lean_object* v_snd_1264_; size_t v_sz_1265_; lean_object* v___x_1266_; 
v___x_1259_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__4);
v_sz_1260_ = lean_array_size(v_regions_1258_);
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_regions_1258_, v_sz_1260_, v___x_1261_, v___x_1259_);
v_fst_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_fst_1263_);
v_snd_1264_ = lean_ctor_get(v___x_1262_, 1);
lean_inc(v_snd_1264_);
lean_dec_ref(v___x_1262_);
v_sz_1265_ = lean_array_size(v_fst_1263_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__6(v_snd_1264_, v_sz_1265_, v___x_1261_, v_fst_1263_);
lean_dec(v_snd_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1267_);
lean_dec_ref(v_regions_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1269_, lean_object* v_m_1270_, lean_object* v_a_1271_, lean_object* v_fallback_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1270_, v_a_1271_, v_fallback_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1274_, lean_object* v_m_1275_, lean_object* v_a_1276_, lean_object* v_fallback_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1274_, v_m_1275_, v_a_1276_, v_fallback_1277_);
lean_dec(v_fallback_1277_);
lean_dec_ref(v_a_1276_);
lean_dec_ref(v_m_1275_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1279_, lean_object* v_m_1280_, lean_object* v_query_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1280_, v_query_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___boxed(lean_object* v_00_u03b2_1283_, lean_object* v_m_1284_, lean_object* v_query_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(v_00_u03b2_1283_, v_m_1284_, v_query_1285_);
lean_dec_ref(v_query_1285_);
lean_dec_ref(v_m_1284_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1287_, lean_object* v_m_1288_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1290_, lean_object* v_m_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1290_, v_m_1291_);
lean_dec_ref(v_m_1291_);
return v_res_1292_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_00_u03b2_1293_, lean_object* v_m_1294_, lean_object* v_a_1295_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___redArg(v_m_1294_, v_a_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_m_1298_, lean_object* v_a_1299_){
_start:
{
uint8_t v_res_1300_; lean_object* v_r_1301_; 
v_res_1300_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_00_u03b2_1297_, v_m_1298_, v_a_1299_);
lean_dec_ref(v_a_1299_);
lean_dec_ref(v_m_1298_);
v_r_1301_ = lean_box(v_res_1300_);
return v_r_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1302_, lean_object* v_m_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_m_1303_, v_a_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1306_, v_m_1307_, v_a_1308_);
lean_dec_ref(v_a_1308_);
lean_dec_ref(v_m_1307_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1310_, lean_object* v_m_1311_, lean_object* v_query_1312_, lean_object* v_x_1313_, lean_object* v_x_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_m_1311_, v_query_1312_, v_x_1313_, v_x_1314_, v_x_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1318_, lean_object* v_m_1319_, lean_object* v_query_1320_, lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_x_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1318_, v_m_1319_, v_query_1320_, v_x_1321_, v_x_1322_, v_x_1323_, v_x_1324_);
lean_dec_ref(v_query_1320_);
lean_dec_ref(v_m_1319_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4(lean_object* v_00_u03b2_1326_, lean_object* v_init_1327_, lean_object* v_b_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___redArg(v_init_1327_, v_b_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1330_, lean_object* v_init_1331_, lean_object* v_b_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4(v_00_u03b2_1330_, v_init_1331_, v_b_1332_);
lean_dec_ref(v_b_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6(lean_object* v_00_u03b2_1334_, lean_object* v_m_1335_, lean_object* v_query_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___redArg(v_m_1335_, v_query_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1338_, lean_object* v_m_1339_, lean_object* v_query_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3_spec__6(v_00_u03b2_1338_, v_m_1339_, v_query_1340_);
lean_dec_ref(v_query_1340_);
lean_dec_ref(v_m_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1342_, lean_object* v_b_1343_, lean_object* v_acc_1344_, lean_object* v_i_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___redArg(v_b_1343_, v_acc_1344_, v_i_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1347_, lean_object* v_b_1348_, lean_object* v_acc_1349_, lean_object* v_i_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2_spec__4_spec__5(v_00_u03b2_1347_, v_b_1348_, v_acc_1349_, v_i_1350_);
lean_dec_ref(v_b_1348_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1352_, size_t v_sz_1353_, size_t v_i_1354_, lean_object* v_b_1355_){
_start:
{
uint8_t v___x_1357_; 
v___x_1357_ = lean_usize_dec_lt(v_i_1354_, v_sz_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_b_1355_);
return v___x_1358_;
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1360_; 
v_a_1359_ = lean_array_uget_borrowed(v_as_1352_, v_i_1354_);
v___x_1360_ = lean_compacted_region_read(v_a_1359_, v_b_1355_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v_snd_1362_; lean_object* v___x_1363_; size_t v___x_1364_; size_t v___x_1365_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_snd_1362_ = lean_ctor_get(v_a_1361_, 1);
lean_inc(v_snd_1362_);
lean_dec(v_a_1361_);
v___x_1363_ = lean_array_push(v_b_1355_, v_snd_1362_);
v___x_1364_ = ((size_t)1ULL);
v___x_1365_ = lean_usize_add(v_i_1354_, v___x_1364_);
v_i_1354_ = v___x_1365_;
v_b_1355_ = v___x_1363_;
goto _start;
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v_b_1355_);
v_a_1367_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1360_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1360_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1375_, lean_object* v_sz_1376_, lean_object* v_i_1377_, lean_object* v_b_1378_, lean_object* v___y_1379_){
_start:
{
size_t v_sz_boxed_1380_; size_t v_i_boxed_1381_; lean_object* v_res_1382_; 
v_sz_boxed_1380_ = lean_unbox_usize(v_sz_1376_);
lean_dec(v_sz_1376_);
v_i_boxed_1381_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_res_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1375_, v_sz_boxed_1380_, v_i_boxed_1381_, v_b_1378_);
lean_dec_ref(v_as_1375_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1385_){
_start:
{
lean_object* v_oleanRegions_1387_; lean_object* v___x_1388_; size_t v_sz_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v_oleanRegions_1387_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1385_);
v___x_1388_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1385_);
v_sz_1389_ = lean_array_size(v___x_1388_);
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1388_, v_sz_1389_, v___x_1390_, v_oleanRegions_1387_);
lean_dec_ref(v___x_1388_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; size_t v_sz_1394_; lean_object* v___x_1395_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l_Lean_ModuleArtifacts_irParts(v_arts_1385_);
v_sz_1394_ = lean_array_size(v___x_1393_);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1393_, v_sz_1394_, v___x_1390_, v_oleanRegions_1387_);
lean_dec_ref(v___x_1393_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1404_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1404_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = l_Array_append___redArg(v_a_1392_, v_a_1396_);
lean_dec(v_a_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_dec(v_a_1392_);
return v___x_1395_;
}
}
else
{
lean_dec_ref(v_arts_1385_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1408_){
_start:
{
if (lean_obj_tag(v_e_1408_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1419_; 
v_a_1410_ = lean_ctor_get(v_e_1408_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_e_1408_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1412_ = v_e_1408_;
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v_e_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1419_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1414_ = lean_io_error_to_string(v_a_1410_);
v___x_1415_ = lean_mk_io_user_error(v___x_1414_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 1);
lean_ctor_set(v___x_1412_, 0, v___x_1415_);
v___x_1417_ = v___x_1412_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1427_; 
v_a_1420_ = lean_ctor_get(v_e_1408_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_e_1408_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1422_ = v_e_1408_;
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v_e_1408_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1427_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v___x_1425_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 0);
v___x_1425_ = v___x_1422_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_a_1420_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1428_, lean_object* v_a_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1431_, lean_object* v_e_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_e_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1435_, v_e_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1439_, lean_object* v___y_1440_, lean_object* v_a_1441_){
_start:
{
lean_object* v_fst_1443_; lean_object* v_snd_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1472_; 
v_fst_1443_ = lean_ctor_get(v_a_1441_, 0);
v_snd_1444_ = lean_ctor_get(v_a_1441_, 1);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_a_1441_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1446_ = v_a_1441_;
v_isShared_1447_ = v_isSharedCheck_1472_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_snd_1444_);
lean_inc(v_fst_1443_);
lean_dec(v_a_1441_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1472_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1448_ = lean_array_get_size(v_a_1439_);
v___x_1449_ = lean_nat_dec_lt(v_snd_1444_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1451_; 
if (v_isShared_1447_ == 0)
{
v___x_1451_ = v___x_1446_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_fst_1443_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_snd_1444_);
v___x_1451_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
else
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1454_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1455_ = lean_array_get_borrowed(v___x_1454_, v_a_1439_, v_snd_1444_);
lean_inc(v___x_1455_);
v___x_1456_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1455_);
if (lean_obj_tag(v___x_1456_) == 0)
{
lean_object* v_a_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v___x_1458_ = l_Array_append___redArg(v_fst_1443_, v_a_1457_);
lean_dec(v_a_1457_);
v___x_1459_ = lean_nat_add(v_snd_1444_, v___y_1440_);
lean_dec(v_snd_1444_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 1, v___x_1459_);
lean_ctor_set(v___x_1446_, 0, v___x_1458_);
v___x_1461_ = v___x_1446_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
v_a_1441_ = v___x_1461_;
goto _start;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_del_object(v___x_1446_);
lean_dec(v_snd_1444_);
lean_dec(v_fst_1443_);
v_a_1464_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1456_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1456_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1473_, lean_object* v___y_1474_, lean_object* v_a_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1473_, v___y_1474_, v_a_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v_a_1473_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1478_, lean_object* v___y_1479_, lean_object* v___x_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1478_, v___y_1479_, v___x_1480_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1491_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1491_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_fst_1487_; lean_object* v___x_1489_; 
v_fst_1487_ = lean_ctor_get(v_a_1483_, 0);
lean_inc(v_fst_1487_);
lean_dec(v_a_1483_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set_tag(v___x_1485_, 1);
lean_ctor_set(v___x_1485_, 0, v_fst_1487_);
v___x_1489_ = v___x_1485_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_fst_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
v_a_1492_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1482_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1482_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 0);
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1500_, lean_object* v___y_1501_, lean_object* v___x_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1500_, v___y_1501_, v___x_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v_a_1500_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1505_, lean_object* v_a_1506_, lean_object* v___y_1507_, lean_object* v_a_1508_, lean_object* v_b_1509_){
_start:
{
uint8_t v___x_1511_; 
v___x_1511_ = lean_nat_dec_lt(v_a_1508_, v_upperBound_1505_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_dec(v_a_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v_a_1506_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_b_1509_);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___f_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1508_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v_a_1508_);
lean_inc(v___y_1507_);
lean_inc_ref(v_a_1506_);
v___f_1516_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1516_, 0, v_a_1506_);
lean_closure_set(v___f_1516_, 1, v___y_1507_);
lean_closure_set(v___f_1516_, 2, v___x_1515_);
v___x_1517_ = lean_io_as_task(v___f_1516_, v___x_1513_);
v___x_1518_ = lean_array_push(v_b_1509_, v___x_1517_);
v___x_1519_ = lean_unsigned_to_nat(1u);
v___x_1520_ = lean_nat_add(v_a_1508_, v___x_1519_);
lean_dec(v_a_1508_);
v_a_1508_ = v___x_1520_;
v_b_1509_ = v___x_1518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1522_, lean_object* v_a_1523_, lean_object* v___y_1524_, lean_object* v_a_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1522_, v_a_1523_, v___y_1524_, v_a_1525_, v_b_1526_);
lean_dec(v_upperBound_1522_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1529_, size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_b_1532_){
_start:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_usize_dec_lt(v_i_1531_, v_sz_1530_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_b_1532_);
return v___x_1535_;
}
else
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_a_1536_ = lean_array_uget_borrowed(v_as_1529_, v_i_1531_);
lean_inc(v_a_1536_);
v___x_1537_ = lean_task_get_own(v_a_1536_);
v___x_1538_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1537_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; size_t v___x_1541_; size_t v___x_1542_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = l_Array_append___redArg(v_b_1532_, v_a_1539_);
lean_dec(v_a_1539_);
v___x_1541_ = ((size_t)1ULL);
v___x_1542_ = lean_usize_add(v_i_1531_, v___x_1541_);
v_i_1531_ = v___x_1542_;
v_b_1532_ = v___x_1540_;
goto _start;
}
else
{
lean_dec_ref(v_b_1532_);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1544_, lean_object* v_sz_1545_, lean_object* v_i_1546_, lean_object* v_b_1547_, lean_object* v___y_1548_){
_start:
{
size_t v_sz_boxed_1549_; size_t v_i_boxed_1550_; lean_object* v_res_1551_; 
v_sz_boxed_1549_ = lean_unbox_usize(v_sz_1545_);
lean_dec(v_sz_1545_);
v_i_boxed_1550_ = lean_unbox_usize(v_i_1546_);
lean_dec(v_i_1546_);
v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1544_, v_sz_boxed_1549_, v_i_boxed_1550_, v_b_1547_);
lean_dec_ref(v_as_1544_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1552_, size_t v_i_1553_, lean_object* v_bs_1554_){
_start:
{
uint8_t v___x_1555_; 
v___x_1555_ = lean_usize_dec_lt(v_i_1553_, v_sz_1552_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_bs_1554_);
return v___x_1556_;
}
else
{
lean_object* v_v_1557_; lean_object* v___x_1558_; 
v_v_1557_ = lean_array_uget_borrowed(v_bs_1554_, v_i_1553_);
lean_inc(v_v_1557_);
v___x_1558_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v_bs_1554_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v_bs_x27_1569_; size_t v___x_1570_; size_t v___x_1571_; lean_object* v___x_1572_; 
v_a_1567_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1568_ = lean_unsigned_to_nat(0u);
v_bs_x27_1569_ = lean_array_uset(v_bs_1554_, v_i_1553_, v___x_1568_);
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_i_1553_, v___x_1570_);
v___x_1572_ = lean_array_uset(v_bs_x27_1569_, v_i_1553_, v_a_1567_);
v_i_1553_ = v___x_1571_;
v_bs_1554_ = v___x_1572_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1574_, lean_object* v_i_1575_, lean_object* v_bs_1576_){
_start:
{
size_t v_sz_boxed_1577_; size_t v_i_boxed_1578_; lean_object* v_res_1579_; 
v_sz_boxed_1577_ = lean_unbox_usize(v_sz_1574_);
lean_dec(v_sz_1574_);
v_i_boxed_1578_ = lean_unbox_usize(v_i_1575_);
lean_dec(v_i_1575_);
v_res_1579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1577_, v_i_boxed_1578_, v_bs_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1582_){
_start:
{
if (lean_obj_tag(v_x_1582_) == 4)
{
lean_object* v_elems_1583_; size_t v_sz_1584_; size_t v___x_1585_; lean_object* v___x_1586_; 
v_elems_1583_ = lean_ctor_get(v_x_1582_, 0);
lean_inc_ref(v_elems_1583_);
lean_dec_ref_known(v_x_1582_, 1);
v_sz_1584_ = lean_array_size(v_elems_1583_);
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1584_, v___x_1585_, v_elems_1583_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1587_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1588_ = lean_unsigned_to_nat(80u);
v___x_1589_ = l_Lean_Json_pretty(v_x_1582_, v___x_1588_);
v___x_1590_ = lean_string_append(v___x_1587_, v___x_1589_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1592_ = lean_string_append(v___x_1590_, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
return v___x_1593_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1597_; uint32_t v___x_1598_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_internal_get_hardware_concurrency(v___x_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1600_ = lean_uint32_to_nat(v___x_1599_);
return v___x_1600_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1602_ = lean_unsigned_to_nat(4u);
v___x_1603_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1604_ = lean_nat_dec_le(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1605_){
_start:
{
lean_object* v___x_1607_; lean_object* v_depsFile_1608_; lean_object* v___x_1609_; 
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1605_);
v_depsFile_1608_ = l_System_FilePath_addExtension(v_fname_1605_, v___x_1607_);
v___x_1609_ = l_IO_FS_readFile(v_depsFile_1608_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1696_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1696_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1696_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_a_1615_; lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Json_parse(v_a_1610_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; 
lean_dec_ref(v_fname_1605_);
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_a_1615_ = v_a_1626_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1625_, 1);
v___x_1628_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; 
lean_dec_ref(v_fname_1605_);
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v_a_1615_ = v_a_1629_;
goto v___jp_1614_;
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___y_1634_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1685_; uint8_t v___x_1695_; 
lean_del_object(v___x_1612_);
lean_dec_ref(v_depsFile_1608_);
v_a_1630_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1628_, 1);
v___x_1631_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1632_ = lean_unsigned_to_nat(4u);
v___x_1695_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1695_ == 0)
{
v___y_1685_ = v___x_1632_;
goto v___jp_1684_;
}
else
{
v___y_1685_ = v___x_1631_;
goto v___jp_1684_;
}
v___jp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = lean_mk_empty_array_with_capacity(v___y_1634_);
v___x_1636_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1630_);
lean_inc(v___y_1634_);
v___x_1637_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1634_, v_a_1630_, v___y_1634_, v___x_1636_, v___x_1635_);
lean_dec(v___y_1634_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; size_t v_sz_1642_; size_t v___x_1643_; lean_object* v___x_1644_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = lean_array_get_size(v_a_1630_);
lean_dec(v_a_1630_);
v___x_1640_ = lean_nat_mul(v___x_1639_, v___x_1632_);
v___x_1641_ = lean_mk_empty_array_with_capacity(v___x_1640_);
lean_dec(v___x_1640_);
v_sz_1642_ = lean_array_size(v_a_1638_);
v___x_1643_ = ((size_t)0ULL);
v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1638_, v_sz_1642_, v___x_1643_, v___x_1641_);
lean_dec(v_a_1638_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = lean_compacted_region_read(v_fname_1605_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_fname_1605_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1655_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1655_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v_fst_1651_; lean_object* v___x_1653_; 
v_fst_1651_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_fst_1651_);
lean_dec(v_a_1647_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_fst_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_fst_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1646_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1646_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec_ref(v_fname_1605_);
v_a_1664_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1644_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1644_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_a_1630_);
lean_dec_ref(v_fname_1605_);
v_a_1672_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1637_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1637_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
v___jp_1680_:
{
uint8_t v___x_1683_; 
v___x_1683_ = lean_nat_dec_le(v___y_1681_, v___y_1682_);
if (v___x_1683_ == 0)
{
lean_dec(v___y_1682_);
v___y_1634_ = v___y_1681_;
goto v___jp_1633_;
}
else
{
lean_dec(v___y_1681_);
v___y_1634_ = v___y_1682_;
goto v___jp_1633_;
}
}
v___jp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1687_ = lean_io_getenv(v___x_1686_);
v___x_1688_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1687_) == 0)
{
v___y_1681_ = v___x_1688_;
v___y_1682_ = v___y_1685_;
goto v___jp_1680_;
}
else
{
lean_object* v_val_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_val_1689_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = lean_string_utf8_byte_size(v_val_1689_);
v___x_1692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1692_, 0, v_val_1689_);
lean_ctor_set(v___x_1692_, 1, v___x_1690_);
lean_ctor_set(v___x_1692_, 2, v___x_1691_);
v___x_1693_ = l_String_Slice_toNat_x3f(v___x_1692_);
lean_dec_ref_known(v___x_1692_, 3);
if (lean_obj_tag(v___x_1693_) == 0)
{
v___y_1681_ = v___x_1688_;
v___y_1682_ = v___y_1685_;
goto v___jp_1680_;
}
else
{
lean_object* v_val_1694_; 
lean_dec(v___y_1685_);
v_val_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_val_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___y_1681_ = v___x_1688_;
v___y_1682_ = v_val_1694_;
goto v___jp_1680_;
}
}
}
}
}
v___jp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1617_ = lean_string_append(v___x_1616_, v_depsFile_1608_);
lean_dec_ref(v_depsFile_1608_);
v___x_1618_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1619_ = lean_string_append(v___x_1617_, v___x_1618_);
v___x_1620_ = lean_string_append(v___x_1619_, v_a_1615_);
lean_dec_ref(v_a_1615_);
v___x_1621_ = lean_mk_io_user_error(v___x_1620_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 1);
lean_ctor_set(v___x_1612_, 0, v___x_1621_);
v___x_1623_ = v___x_1612_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_depsFile_1608_);
lean_dec_ref(v_fname_1605_);
v_a_1697_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1609_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1609_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1705_, lean_object* v_a_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1708_, lean_object* v___y_1709_, lean_object* v_inst_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1708_, v___y_1709_, v_a_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1714_, lean_object* v___y_1715_, lean_object* v_inst_1716_, lean_object* v_a_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1714_, v___y_1715_, v_inst_1716_, v_a_1717_);
lean_dec(v___y_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1720_, lean_object* v_a_1721_, lean_object* v___y_1722_, lean_object* v_inst_1723_, lean_object* v_R_1724_, lean_object* v_a_1725_, lean_object* v_b_1726_, lean_object* v_c_1727_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1720_, v_a_1721_, v___y_1722_, v_a_1725_, v_b_1726_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1730_, lean_object* v_a_1731_, lean_object* v___y_1732_, lean_object* v_inst_1733_, lean_object* v_R_1734_, lean_object* v_a_1735_, lean_object* v_b_1736_, lean_object* v_c_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1730_, v_a_1731_, v___y_1732_, v_inst_1733_, v_R_1734_, v_a_1735_, v_b_1736_, v_c_1737_);
lean_dec(v_upperBound_1730_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1740_, size_t v_sz_1741_, size_t v_i_1742_, lean_object* v_b_1743_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_lt(v_i_1742_, v_sz_1741_);
if (v___x_1745_ == 0)
{
return v_b_1743_;
}
else
{
lean_object* v_a_1746_; lean_object* v_cancelTk_x3f_1747_; lean_object* v___x_1748_; 
v_a_1746_ = lean_array_uget_borrowed(v_as_1740_, v_i_1742_);
v_cancelTk_x3f_1747_ = lean_ctor_get(v_a_1746_, 2);
v___x_1748_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1747_) == 1)
{
lean_object* v_val_1755_; lean_object* v___x_1756_; 
v_val_1755_ = lean_ctor_get(v_cancelTk_x3f_1747_, 0);
v___x_1756_ = l_IO_CancelToken_set(v_val_1755_);
goto v___jp_1749_;
}
else
{
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; 
lean_inc(v_a_1746_);
v___x_1750_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1746_);
v___x_1751_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1750_);
lean_dec(v___x_1750_);
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1742_, v___x_1752_);
v_i_1742_ = v___x_1753_;
v_b_1743_ = v___x_1748_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1757_){
_start:
{
lean_object* v_children_1759_; lean_object* v___x_1760_; size_t v_sz_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v_children_1759_ = lean_ctor_get(v_s_1757_, 1);
v___x_1760_ = lean_box(0);
v_sz_1761_ = lean_array_size(v_children_1759_);
v___x_1762_ = ((size_t)0ULL);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1759_, v_sz_1761_, v___x_1762_, v___x_1760_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1764_);
lean_dec_ref(v_s_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1767_, lean_object* v_sz_1768_, lean_object* v_i_1769_, lean_object* v_b_1770_, lean_object* v___y_1771_){
_start:
{
size_t v_sz_boxed_1772_; size_t v_i_boxed_1773_; lean_object* v_res_1774_; 
v_sz_boxed_1772_ = lean_unbox_usize(v_sz_1768_);
lean_dec(v_sz_1768_);
v_i_boxed_1773_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1767_, v_sz_boxed_1772_, v_i_boxed_1773_, v_b_1770_);
lean_dec_ref(v_as_1767_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1775_, lean_object* v_m_1776_){
_start:
{
lean_object* v_result_x3f_1777_; 
v_result_x3f_1777_ = lean_ctor_get(v_snap_1775_, 4);
lean_inc(v_result_x3f_1777_);
if (lean_obj_tag(v_result_x3f_1777_) == 1)
{
lean_object* v_val_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1877_; 
v_val_1778_ = lean_ctor_get(v_result_x3f_1777_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_result_x3f_1777_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1780_ = v_result_x3f_1777_;
v_isShared_1781_ = v_isSharedCheck_1877_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_val_1778_);
lean_dec(v_result_x3f_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1877_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_toSnapshot_1782_; lean_object* v_metaSnap_1783_; lean_object* v_ictx_1784_; lean_object* v_stx_1785_; lean_object* v_parserState_1786_; lean_object* v_processedSnap_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1876_; 
v_toSnapshot_1782_ = lean_ctor_get(v_snap_1775_, 0);
v_metaSnap_1783_ = lean_ctor_get(v_snap_1775_, 1);
v_ictx_1784_ = lean_ctor_get(v_snap_1775_, 2);
v_stx_1785_ = lean_ctor_get(v_snap_1775_, 3);
v_parserState_1786_ = lean_ctor_get(v_val_1778_, 0);
v_processedSnap_1787_ = lean_ctor_get(v_val_1778_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_val_1778_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1789_ = v_val_1778_;
v_isShared_1790_ = v_isSharedCheck_1876_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_processedSnap_1787_);
lean_inc(v_parserState_1786_);
lean_dec(v_val_1778_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1876_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_processed_1791_; lean_object* v_result_x3f_1792_; 
v_processed_1791_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1787_);
v_result_x3f_1792_ = lean_ctor_get(v_processed_1791_, 2);
lean_inc(v_result_x3f_1792_);
if (lean_obj_tag(v_result_x3f_1792_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1875_; 
v_val_1793_ = lean_ctor_get(v_result_x3f_1792_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_result_x3f_1792_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1795_ = v_result_x3f_1792_;
v_isShared_1796_ = v_isSharedCheck_1875_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_val_1793_);
lean_dec(v_result_x3f_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1875_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v_cmdState_1797_; lean_object* v_toSnapshot_1798_; lean_object* v_metaSnap_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1873_; 
v_cmdState_1797_ = lean_ctor_get(v_val_1793_, 0);
lean_inc_ref(v_cmdState_1797_);
v_toSnapshot_1798_ = lean_ctor_get(v_processed_1791_, 0);
v_metaSnap_1799_ = lean_ctor_get(v_processed_1791_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_processed_1791_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_processed_1791_, 2);
lean_dec(v_unused_1874_);
v___x_1801_ = v_processed_1791_;
v_isShared_1802_ = v_isSharedCheck_1873_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_metaSnap_1799_);
lean_inc(v_toSnapshot_1798_);
lean_dec(v_processed_1791_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1873_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_firstCmdSnap_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1871_; 
v_firstCmdSnap_1803_ = lean_ctor_get(v_val_1793_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_val_1793_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v_val_1793_, 0);
lean_dec(v_unused_1872_);
v___x_1805_ = v_val_1793_;
v_isShared_1806_ = v_isSharedCheck_1871_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_firstCmdSnap_1803_);
lean_dec(v_val_1793_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1871_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_env_1807_; lean_object* v_messages_1808_; lean_object* v_scopes_1809_; lean_object* v_usedQuotCtxts_1810_; lean_object* v_nextMacroScope_1811_; lean_object* v_maxRecDepth_1812_; lean_object* v_ngen_1813_; lean_object* v_auxDeclNGen_1814_; lean_object* v_infoState_1815_; lean_object* v_traceState_1816_; lean_object* v_snapshotTasks_1817_; lean_object* v_prevLinterStates_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1870_; 
v_env_1807_ = lean_ctor_get(v_cmdState_1797_, 0);
v_messages_1808_ = lean_ctor_get(v_cmdState_1797_, 1);
v_scopes_1809_ = lean_ctor_get(v_cmdState_1797_, 2);
v_usedQuotCtxts_1810_ = lean_ctor_get(v_cmdState_1797_, 3);
v_nextMacroScope_1811_ = lean_ctor_get(v_cmdState_1797_, 4);
v_maxRecDepth_1812_ = lean_ctor_get(v_cmdState_1797_, 5);
v_ngen_1813_ = lean_ctor_get(v_cmdState_1797_, 6);
v_auxDeclNGen_1814_ = lean_ctor_get(v_cmdState_1797_, 7);
v_infoState_1815_ = lean_ctor_get(v_cmdState_1797_, 8);
v_traceState_1816_ = lean_ctor_get(v_cmdState_1797_, 9);
v_snapshotTasks_1817_ = lean_ctor_get(v_cmdState_1797_, 10);
v_prevLinterStates_1818_ = lean_ctor_get(v_cmdState_1797_, 11);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_cmdState_1797_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1820_ = v_cmdState_1797_;
v_isShared_1821_ = v_isSharedCheck_1870_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_prevLinterStates_1818_);
lean_inc(v_snapshotTasks_1817_);
lean_inc(v_traceState_1816_);
lean_inc(v_infoState_1815_);
lean_inc(v_auxDeclNGen_1814_);
lean_inc(v_ngen_1813_);
lean_inc(v_maxRecDepth_1812_);
lean_inc(v_nextMacroScope_1811_);
lean_inc(v_usedQuotCtxts_1810_);
lean_inc(v_scopes_1809_);
lean_inc(v_messages_1808_);
lean_inc(v_env_1807_);
lean_dec(v_cmdState_1797_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1870_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v_mainModule_1823_; uint8_t v___x_1824_; 
v___x_1822_ = l_Lean_Environment_header(v_env_1807_);
v_mainModule_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_mainModule_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_name_eq(v_mainModule_1823_, v_m_1776_);
lean_dec(v_mainModule_1823_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1864_; 
lean_inc(v_stx_1785_);
lean_inc_ref(v_ictx_1784_);
lean_inc_ref(v_metaSnap_1783_);
lean_inc_ref(v_toSnapshot_1782_);
v_isSharedCheck_1864_ = !lean_is_exclusive(v_snap_1775_);
if (v_isSharedCheck_1864_ == 0)
{
lean_object* v_unused_1865_; lean_object* v_unused_1866_; lean_object* v_unused_1867_; lean_object* v_unused_1868_; lean_object* v_unused_1869_; 
v_unused_1865_ = lean_ctor_get(v_snap_1775_, 4);
lean_dec(v_unused_1865_);
v_unused_1866_ = lean_ctor_get(v_snap_1775_, 3);
lean_dec(v_unused_1866_);
v_unused_1867_ = lean_ctor_get(v_snap_1775_, 2);
lean_dec(v_unused_1867_);
v_unused_1868_ = lean_ctor_get(v_snap_1775_, 1);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v_snap_1775_, 0);
lean_dec(v_unused_1869_);
v___x_1826_ = v_snap_1775_;
v_isShared_1827_ = v_isSharedCheck_1864_;
goto v_resetjp_1825_;
}
else
{
lean_dec(v_snap_1775_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1864_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_idx_1828_; lean_object* v_parentIdxs_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1862_; 
v_idx_1828_ = lean_ctor_get(v_auxDeclNGen_1814_, 1);
v_parentIdxs_1829_ = lean_ctor_get(v_auxDeclNGen_1814_, 2);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_auxDeclNGen_1814_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v_auxDeclNGen_1814_, 0);
lean_dec(v_unused_1863_);
v___x_1831_ = v_auxDeclNGen_1814_;
v_isShared_1832_ = v_isSharedCheck_1862_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_parentIdxs_1829_);
lean_inc(v_idx_1828_);
lean_dec(v_auxDeclNGen_1814_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1862_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_newEnv_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v_newEnv_1833_ = l_Lean_Environment_setMainModule(v_env_1807_, v_m_1776_);
v___x_1834_ = lean_box(0);
v___x_1835_ = l_Lean_mkPrivateName(v_newEnv_1833_, v___x_1834_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1835_);
v___x_1837_ = v___x_1831_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_idx_1828_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_parentIdxs_1829_);
v___x_1837_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v_newCmdState_1839_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 7, v___x_1837_);
lean_ctor_set(v___x_1820_, 0, v_newEnv_1833_);
v_newCmdState_1839_ = v___x_1820_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_newEnv_1833_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_messages_1808_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_scopes_1809_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_usedQuotCtxts_1810_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_nextMacroScope_1811_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_maxRecDepth_1812_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_ngen_1813_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v_infoState_1815_);
lean_ctor_set(v_reuseFailAlloc_1860_, 9, v_traceState_1816_);
lean_ctor_set(v_reuseFailAlloc_1860_, 10, v_snapshotTasks_1817_);
lean_ctor_set(v_reuseFailAlloc_1860_, 11, v_prevLinterStates_1818_);
v_newCmdState_1839_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v_newCmdState_1839_);
v___x_1841_ = v___x_1805_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_newCmdState_1839_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_firstCmdSnap_1803_);
v___x_1841_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1841_);
v___x_1843_ = v___x_1795_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v_newProcessed_1845_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 2, v___x_1843_);
v_newProcessed_1845_ = v___x_1801_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_toSnapshot_1798_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_metaSnap_1799_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v___x_1843_);
v_newProcessed_1845_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1846_ = lean_box(0);
v___x_1847_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1846_, v_newProcessed_1845_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 1, v___x_1847_);
v___x_1849_ = v___x_1789_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_parserState_1786_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1849_);
v___x_1851_ = v___x_1780_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 4, v___x_1851_);
v___x_1853_ = v___x_1826_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_toSnapshot_1782_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_metaSnap_1783_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_ictx_1784_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_stx_1785_);
lean_ctor_set(v_reuseFailAlloc_1854_, 4, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1820_);
lean_dec(v_prevLinterStates_1818_);
lean_dec_ref(v_snapshotTasks_1817_);
lean_dec_ref(v_traceState_1816_);
lean_dec_ref(v_infoState_1815_);
lean_dec_ref(v_auxDeclNGen_1814_);
lean_dec_ref(v_ngen_1813_);
lean_dec(v_maxRecDepth_1812_);
lean_dec(v_nextMacroScope_1811_);
lean_dec(v_usedQuotCtxts_1810_);
lean_dec(v_scopes_1809_);
lean_dec_ref(v_messages_1808_);
lean_dec_ref(v_env_1807_);
lean_del_object(v___x_1805_);
lean_dec_ref(v_firstCmdSnap_1803_);
lean_del_object(v___x_1801_);
lean_dec_ref(v_metaSnap_1799_);
lean_dec_ref(v_toSnapshot_1798_);
lean_del_object(v___x_1795_);
lean_del_object(v___x_1789_);
lean_dec_ref(v_parserState_1786_);
lean_del_object(v___x_1780_);
lean_dec(v_m_1776_);
return v_snap_1775_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1792_);
lean_dec(v_processed_1791_);
lean_del_object(v___x_1789_);
lean_dec_ref(v_parserState_1786_);
lean_del_object(v___x_1780_);
lean_dec(v_m_1776_);
return v_snap_1775_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1777_);
lean_dec(v_m_1776_);
return v_snap_1775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1878_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1881_, lean_object* v_a_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1884_, lean_object* v_incr_1885_, lean_object* v_res_1886_){
_start:
{
lean_object* v_cmdState_1888_; lean_object* v_env_1889_; lean_object* v_initModIdxs_1890_; lean_object* v___x_1891_; 
v_cmdState_1888_ = lean_ctor_get(v_res_1886_, 0);
lean_inc_ref(v_cmdState_1888_);
lean_dec_ref(v_res_1886_);
v_env_1889_ = lean_ctor_get(v_cmdState_1888_, 0);
lean_inc_ref(v_env_1889_);
lean_dec_ref(v_cmdState_1888_);
v_initModIdxs_1890_ = lean_ctor_get(v_incr_1885_, 1);
v___x_1891_ = l_Lean_runInitAttrsForModules(v_env_1889_, v_initModIdxs_1890_, v_opts_1884_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1892_, lean_object* v_incr_1893_, lean_object* v_res_1894_, lean_object* v_a_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1892_, v_incr_1893_, v_res_1894_);
lean_dec_ref(v_incr_1893_);
lean_dec_ref(v_opts_1892_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_enable_initializer_execution();
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1904_, lean_object* v_incrFile_1905_, lean_object* v_toSave_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v_regions_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1908_ = l_Lean_Environment_header(v_env_1904_);
v_regions_1909_ = lean_ctor_get(v___x_1908_, 2);
lean_inc_ref(v_regions_1909_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1911_ = lean_box(0);
v___x_1912_ = 1;
v___x_1913_ = lean_compacted_region_save(v_incrFile_1905_, v___x_1910_, v_toSave_1906_, v_regions_1909_, v___x_1911_, v___x_1912_);
lean_dec_ref(v_regions_1909_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1914_, lean_object* v_incrFile_1915_, lean_object* v_toSave_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1914_, v_incrFile_1915_, v_toSave_1916_);
lean_dec_ref(v_toSave_1916_);
lean_dec_ref(v_incrFile_1915_);
lean_dec_ref(v_env_1914_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1919_, lean_object* v_opt_1920_){
_start:
{
lean_object* v_name_1921_; lean_object* v_map_1922_; lean_object* v___x_1923_; 
v_name_1921_ = lean_ctor_get(v_opt_1920_, 0);
v_map_1922_ = lean_ctor_get(v_opts_1919_, 0);
v___x_1923_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1922_, v_name_1921_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_box(0);
return v___x_1924_;
}
else
{
lean_object* v_val_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1934_; 
v_val_1925_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1927_ = v___x_1923_;
v_isShared_1928_ = v_isSharedCheck_1934_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_val_1925_);
lean_dec(v___x_1923_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1934_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
if (lean_obj_tag(v_val_1925_) == 0)
{
lean_object* v_v_1929_; lean_object* v___x_1931_; 
v_v_1929_ = lean_ctor_get(v_val_1925_, 0);
lean_inc_ref(v_v_1929_);
lean_dec_ref_known(v_val_1925_, 1);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v_v_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_v_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
else
{
lean_object* v___x_1933_; 
lean_del_object(v___x_1927_);
lean_dec(v_val_1925_);
v___x_1933_ = lean_box(0);
return v___x_1933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1935_, lean_object* v_opt_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1935_, v_opt_1936_);
lean_dec_ref(v_opt_1936_);
lean_dec_ref(v_opts_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1938_, lean_object* v_opt_1939_){
_start:
{
lean_object* v_name_1940_; lean_object* v_defValue_1941_; lean_object* v_map_1942_; lean_object* v___x_1943_; 
v_name_1940_ = lean_ctor_get(v_opt_1939_, 0);
v_defValue_1941_ = lean_ctor_get(v_opt_1939_, 1);
v_map_1942_ = lean_ctor_get(v_opts_1938_, 0);
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1942_, v_name_1940_);
if (lean_obj_tag(v___x_1943_) == 0)
{
uint8_t v___x_1944_; 
v___x_1944_ = lean_unbox(v_defValue_1941_);
return v___x_1944_;
}
else
{
lean_object* v_val_1945_; 
v_val_1945_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_val_1945_);
lean_dec_ref_known(v___x_1943_, 1);
if (lean_obj_tag(v_val_1945_) == 1)
{
uint8_t v_v_1946_; 
v_v_1946_ = lean_ctor_get_uint8(v_val_1945_, 0);
lean_dec_ref_known(v_val_1945_, 0);
return v_v_1946_;
}
else
{
uint8_t v___x_1947_; 
lean_dec(v_val_1945_);
v___x_1947_ = lean_unbox(v_defValue_1941_);
return v___x_1947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1948_, lean_object* v_opt_1949_){
_start:
{
uint8_t v_res_1950_; lean_object* v_r_1951_; 
v_res_1950_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1948_, v_opt_1949_);
lean_dec_ref(v_opt_1949_);
lean_dec_ref(v_opts_1948_);
v_r_1951_ = lean_box(v_res_1950_);
return v_r_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1952_, lean_object* v_x_1953_, lean_object* v_hOpt_1954_){
_start:
{
lean_inc_ref(v_hOpt_1954_);
return v_hOpt_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1955_, lean_object* v_x_1956_, lean_object* v_hOpt_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Elab_runFrontend___lam__0(v_x_1955_, v_x_1956_, v_hOpt_1957_);
lean_dec_ref(v_hOpt_1957_);
lean_dec_ref(v_x_1956_);
lean_dec(v_x_1955_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(size_t v_sz_1959_, size_t v_i_1960_, lean_object* v_bs_1961_){
_start:
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_usize_dec_lt(v_i_1960_, v_sz_1959_);
if (v___x_1962_ == 0)
{
return v_bs_1961_;
}
else
{
lean_object* v_v_1963_; lean_object* v___x_1964_; lean_object* v_bs_x27_1965_; lean_object* v___x_1966_; size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v_v_1963_ = lean_array_uget(v_bs_1961_, v_i_1960_);
v___x_1964_ = lean_unsigned_to_nat(0u);
v_bs_x27_1965_ = lean_array_uset(v_bs_1961_, v_i_1960_, v___x_1964_);
v___x_1966_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1963_);
v___x_1967_ = ((size_t)1ULL);
v___x_1968_ = lean_usize_add(v_i_1960_, v___x_1967_);
v___x_1969_ = lean_array_uset(v_bs_x27_1965_, v_i_1960_, v___x_1966_);
v_i_1960_ = v___x_1968_;
v_bs_1961_ = v___x_1969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6___boxed(lean_object* v_sz_1971_, lean_object* v_i_1972_, lean_object* v_bs_1973_){
_start:
{
size_t v_sz_boxed_1974_; size_t v_i_boxed_1975_; lean_object* v_res_1976_; 
v_sz_boxed_1974_ = lean_unbox_usize(v_sz_1971_);
lean_dec(v_sz_1971_);
v_i_boxed_1975_ = lean_unbox_usize(v_i_1972_);
lean_dec(v_i_1972_);
v_res_1976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(v_sz_boxed_1974_, v_i_boxed_1975_, v_bs_1973_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_a_1977_){
_start:
{
size_t v_sz_1978_; size_t v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_sz_1978_ = lean_array_size(v_a_1977_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(v_sz_1978_, v___x_1979_, v_a_1977_);
v___x_1981_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_env_1982_, uint8_t v___x_1983_, lean_object* v_incrFile_1984_, lean_object* v_snapToSave_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v_regions_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = l_Lean_Environment_header(v_env_1982_);
v_regions_1988_ = lean_ctor_get(v___x_1987_, 2);
lean_inc_ref(v_regions_1988_);
lean_dec_ref(v___x_1987_);
v___x_1989_ = l_Lean_getRegularInitAttrModIdxs(v_env_1982_);
v___x_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_snapToSave_1985_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_compacted_region_save(v_incrFile_1984_, v___x_1991_, v___x_1990_, v_regions_1988_, v___x_1992_, v___x_1983_);
lean_dec_ref_known(v___x_1990_, 2);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
v___x_1995_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1988_);
lean_dec_ref(v_regions_1988_);
v___x_1996_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1997_ = l_System_FilePath_addExtension(v_incrFile_1984_, v___x_1996_);
v___x_1998_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3(v___x_1995_);
v___x_1999_ = l_Lean_Json_compress(v___x_1998_);
v___x_2000_ = l_IO_FS_writeFile(v___x_1997_, v___x_1999_);
lean_dec_ref(v___x_1999_);
lean_dec_ref(v___x_1997_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2008_; 
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_2000_, 0);
lean_dec(v_unused_2009_);
v___x_2002_ = v___x_2000_;
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
else
{
lean_dec(v___x_2000_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2008_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2004_ = lean_runtime_forget(v_a_1994_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
lean_dec(v_a_1994_);
return v___x_2000_;
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec_ref(v_regions_1988_);
lean_dec_ref(v_incrFile_1984_);
v_a_2010_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1993_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1993_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_env_2018_, lean_object* v___x_2019_, lean_object* v_incrFile_2020_, lean_object* v_snapToSave_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v___x_5993__boxed_2023_; lean_object* v_res_2024_; 
v___x_5993__boxed_2023_ = lean_unbox(v___x_2019_);
v_res_2024_ = l_Lean_Elab_runFrontend___lam__1(v_env_2018_, v___x_5993__boxed_2023_, v_incrFile_2020_, v_snapToSave_2021_);
lean_dec_ref(v_env_2018_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_fileMap_2025_, lean_object* v_env_2026_, lean_object* v___x_2027_, lean_object* v_opts_2028_, lean_object* v_val_2029_, uint8_t v___x_2030_, uint8_t v_a_2031_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = l_Lean_Linter_recordLints(v_fileMap_2025_, v_env_2026_, v___x_2027_);
v___x_2034_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_2035_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_2028_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_writeModule(v___x_2033_, v_val_2029_, v___x_2030_);
return v___x_2036_;
}
else
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_writeModule(v___x_2033_, v_val_2029_, v_a_2031_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_fileMap_2038_, lean_object* v_env_2039_, lean_object* v___x_2040_, lean_object* v_opts_2041_, lean_object* v_val_2042_, lean_object* v___x_2043_, lean_object* v_a_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v___x_6064__boxed_2046_; uint8_t v_a_6065__boxed_2047_; lean_object* v_res_2048_; 
v___x_6064__boxed_2046_ = lean_unbox(v___x_2043_);
v_a_6065__boxed_2047_ = lean_unbox(v_a_2044_);
v_res_2048_ = l_Lean_Elab_runFrontend___lam__2(v_fileMap_2038_, v_env_2039_, v___x_2040_, v_opts_2041_, v_val_2042_, v___x_6064__boxed_2046_, v_a_6065__boxed_2047_);
lean_dec_ref(v_opts_2041_);
lean_dec_ref(v___x_2040_);
lean_dec_ref(v_fileMap_2038_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_2049_, size_t v_i_2050_, size_t v_stop_2051_, lean_object* v_b_2052_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_usize_dec_eq(v_i_2050_, v_stop_2051_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_array_uget_borrowed(v_as_2049_, v_i_2050_);
lean_inc(v___x_2055_);
v___x_2056_ = lean_load_dynlib(v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; size_t v___x_2058_; size_t v___x_2059_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2050_, v___x_2058_);
v_i_2050_ = v___x_2059_;
v_b_2052_ = v_a_2057_;
goto _start;
}
else
{
return v___x_2056_;
}
}
else
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2061_, 0, v_b_2052_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_2062_, lean_object* v_i_2063_, lean_object* v_stop_2064_, lean_object* v_b_2065_, lean_object* v___y_2066_){
_start:
{
size_t v_i_boxed_2067_; size_t v_stop_boxed_2068_; lean_object* v_res_2069_; 
v_i_boxed_2067_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_stop_boxed_2068_ = lean_unbox_usize(v_stop_2064_);
lean_dec(v_stop_2064_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2062_, v_i_boxed_2067_, v_stop_boxed_2068_, v_b_2065_);
lean_dec_ref(v_as_2062_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_setup_x3f_2070_, lean_object* v___f_2071_, lean_object* v___x_2072_, lean_object* v_plugins_2073_, uint32_t v_trustLevel_2074_, uint8_t v___x_2075_, lean_object* v_mainModuleName_2076_, lean_object* v_stx_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___y_2081_; uint8_t v___y_2082_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; 
if (lean_obj_tag(v_setup_x3f_2070_) == 1)
{
lean_object* v_val_2094_; lean_object* v_name_2095_; lean_object* v_package_x3f_2096_; uint8_t v_isModule_2097_; lean_object* v_imports_x3f_2098_; lean_object* v_importArts_2099_; lean_object* v_dynlibs_2100_; lean_object* v_plugins_2101_; lean_object* v_options_2102_; lean_object* v___y_2109_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
lean_dec(v_mainModuleName_2076_);
v_val_2094_ = lean_ctor_get(v_setup_x3f_2070_, 0);
lean_inc(v_val_2094_);
lean_dec_ref_known(v_setup_x3f_2070_, 1);
v_name_2095_ = lean_ctor_get(v_val_2094_, 0);
lean_inc(v_name_2095_);
v_package_x3f_2096_ = lean_ctor_get(v_val_2094_, 1);
lean_inc(v_package_x3f_2096_);
v_isModule_2097_ = lean_ctor_get_uint8(v_val_2094_, sizeof(void*)*7);
v_imports_x3f_2098_ = lean_ctor_get(v_val_2094_, 2);
lean_inc(v_imports_x3f_2098_);
v_importArts_2099_ = lean_ctor_get(v_val_2094_, 3);
lean_inc(v_importArts_2099_);
v_dynlibs_2100_ = lean_ctor_get(v_val_2094_, 4);
lean_inc_ref(v_dynlibs_2100_);
v_plugins_2101_ = lean_ctor_get(v_val_2094_, 5);
lean_inc_ref(v_plugins_2101_);
v_options_2102_ = lean_ctor_get(v_val_2094_, 6);
lean_inc(v_options_2102_);
lean_dec(v_val_2094_);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_array_get_size(v_dynlibs_2100_);
v___x_2120_ = lean_nat_dec_lt(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_dec_ref(v_dynlibs_2100_);
goto v___jp_2103_;
}
else
{
lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_nat_dec_le(v___x_2119_, v___x_2119_);
if (v___x_2122_ == 0)
{
if (v___x_2120_ == 0)
{
lean_dec_ref(v_dynlibs_2100_);
goto v___jp_2103_;
}
else
{
size_t v___x_2123_; size_t v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = lean_usize_of_nat(v___x_2119_);
v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2100_, v___x_2123_, v___x_2124_, v___x_2121_);
lean_dec_ref(v_dynlibs_2100_);
v___y_2109_ = v___x_2125_;
goto v___jp_2108_;
}
}
else
{
size_t v___x_2126_; size_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = ((size_t)0ULL);
v___x_2127_ = lean_usize_of_nat(v___x_2119_);
v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2100_, v___x_2126_, v___x_2127_, v___x_2121_);
lean_dec_ref(v_dynlibs_2100_);
v___y_2109_ = v___x_2128_;
goto v___jp_2108_;
}
}
v___jp_2103_:
{
uint8_t v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2077_);
v___x_2105_ = lean_strict_or(v_isModule_2097_, v___x_2104_);
if (lean_obj_tag(v_imports_x3f_2098_) == 0)
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2077_, v___x_2075_);
v___y_2081_ = v_name_2095_;
v___y_2082_ = v___x_2105_;
v___y_2083_ = v_importArts_2099_;
v___y_2084_ = v_plugins_2101_;
v___y_2085_ = v_options_2102_;
v___y_2086_ = v_package_x3f_2096_;
v___y_2087_ = v___x_2106_;
goto v___jp_2080_;
}
else
{
lean_object* v_val_2107_; 
lean_dec(v_stx_2077_);
v_val_2107_ = lean_ctor_get(v_imports_x3f_2098_, 0);
lean_inc(v_val_2107_);
lean_dec_ref_known(v_imports_x3f_2098_, 1);
v___y_2081_ = v_name_2095_;
v___y_2082_ = v___x_2105_;
v___y_2083_ = v_importArts_2099_;
v___y_2084_ = v_plugins_2101_;
v___y_2085_ = v_options_2102_;
v___y_2086_ = v_package_x3f_2096_;
v___y_2087_ = v_val_2107_;
goto v___jp_2080_;
}
}
v___jp_2108_:
{
if (lean_obj_tag(v___y_2109_) == 0)
{
lean_dec_ref_known(v___y_2109_, 1);
goto v___jp_2103_;
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec(v_options_2102_);
lean_dec_ref(v_plugins_2101_);
lean_dec(v_importArts_2099_);
lean_dec(v_imports_x3f_2098_);
lean_dec(v_package_x3f_2096_);
lean_dec(v_name_2095_);
lean_dec(v_stx_2077_);
lean_dec_ref(v_plugins_2073_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v___f_2071_);
v_a_2110_ = lean_ctor_get(v___y_2109_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___y_2109_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___y_2109_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___y_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
else
{
lean_object* v___x_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
lean_dec_ref(v___f_2071_);
lean_dec(v_setup_x3f_2070_);
v___x_2129_ = lean_box(0);
v___x_2130_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2077_);
v___x_2131_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2077_, v___x_2075_);
v___x_2132_ = lean_box(1);
v___x_2133_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2133_, 0, v_mainModuleName_2076_);
lean_ctor_set(v___x_2133_, 1, v___x_2129_);
lean_ctor_set(v___x_2133_, 2, v___x_2131_);
lean_ctor_set(v___x_2133_, 3, v___x_2072_);
lean_ctor_set(v___x_2133_, 4, v___x_2132_);
lean_ctor_set(v___x_2133_, 5, v_plugins_2073_);
lean_ctor_set_uint8(v___x_2133_, sizeof(void*)*6 + 4, v___x_2130_);
lean_ctor_set_uint32(v___x_2133_, sizeof(void*)*6, v_trustLevel_2074_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
v___jp_2080_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2088_ = l_Lean_LeanOptions_toOptions(v___y_2085_);
v___x_2089_ = l_Lean_Options_mergeBy(v___f_2071_, v___x_2072_, v___x_2088_);
v___x_2090_ = l_Array_append___redArg(v_plugins_2073_, v___y_2084_);
lean_dec_ref(v___y_2084_);
v___x_2091_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2091_, 0, v___y_2081_);
lean_ctor_set(v___x_2091_, 1, v___y_2086_);
lean_ctor_set(v___x_2091_, 2, v___y_2087_);
lean_ctor_set(v___x_2091_, 3, v___x_2089_);
lean_ctor_set(v___x_2091_, 4, v___y_2083_);
lean_ctor_set(v___x_2091_, 5, v___x_2090_);
lean_ctor_set_uint8(v___x_2091_, sizeof(void*)*6 + 4, v___y_2082_);
lean_ctor_set_uint32(v___x_2091_, sizeof(void*)*6, v_trustLevel_2074_);
v___x_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_setup_x3f_2136_, lean_object* v___f_2137_, lean_object* v___x_2138_, lean_object* v_plugins_2139_, lean_object* v_trustLevel_2140_, lean_object* v___x_2141_, lean_object* v_mainModuleName_2142_, lean_object* v_stx_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
uint32_t v_trustLevel_boxed_2146_; uint8_t v___x_6109__boxed_2147_; lean_object* v_res_2148_; 
v_trustLevel_boxed_2146_ = lean_unbox_uint32(v_trustLevel_2140_);
lean_dec(v_trustLevel_2140_);
v___x_6109__boxed_2147_ = lean_unbox(v___x_2141_);
v_res_2148_ = l_Lean_Elab_runFrontend___lam__3(v_setup_x3f_2136_, v___f_2137_, v___x_2138_, v_plugins_2139_, v_trustLevel_boxed_2146_, v___x_6109__boxed_2147_, v_mainModuleName_2142_, v_stx_2143_, v___y_2144_);
lean_dec_ref(v___y_2144_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_val_2149_, lean_object* v_initModIdxs_2150_, lean_object* v___x_2151_){
_start:
{
lean_object* v_cmdState_2153_; lean_object* v_env_2154_; lean_object* v___x_2155_; 
v_cmdState_2153_ = lean_ctor_get(v_val_2149_, 0);
lean_inc_ref(v_cmdState_2153_);
lean_dec_ref(v_val_2149_);
v_env_2154_ = lean_ctor_get(v_cmdState_2153_, 0);
lean_inc_ref(v_env_2154_);
lean_dec_ref(v_cmdState_2153_);
v___x_2155_ = l_Lean_runInitAttrsForModules(v_env_2154_, v_initModIdxs_2150_, v___x_2151_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_val_2156_, lean_object* v_initModIdxs_2157_, lean_object* v___x_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Elab_runFrontend___lam__4(v_val_2156_, v_initModIdxs_2157_, v___x_2158_);
lean_dec_ref(v___x_2158_);
lean_dec_ref(v_initModIdxs_2157_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2164_, lean_object* v_k_2165_, uint8_t v_v_2166_){
_start:
{
lean_object* v_map_2167_; uint8_t v_hasTrace_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2182_; 
v_map_2167_ = lean_ctor_get(v_o_2164_, 0);
v_hasTrace_2168_ = lean_ctor_get_uint8(v_o_2164_, sizeof(void*)*1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_o_2164_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2170_ = v_o_2164_;
v_isShared_2171_ = v_isSharedCheck_2182_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_map_2167_);
lean_dec(v_o_2164_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2182_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2172_, 0, v_v_2166_);
lean_inc(v_k_2165_);
v___x_2173_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2165_, v___x_2172_, v_map_2167_);
if (v_hasTrace_2168_ == 0)
{
lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2177_; 
v___x_2174_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2175_ = l_Lean_Name_isPrefixOf(v___x_2174_, v_k_2165_);
lean_dec(v_k_2165_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2173_);
v___x_2177_ = v___x_2170_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2173_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_ctor_set_uint8(v___x_2177_, sizeof(void*)*1, v___x_2175_);
return v___x_2177_;
}
}
else
{
lean_object* v___x_2180_; 
lean_dec(v_k_2165_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2173_);
v___x_2180_ = v___x_2170_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2173_);
lean_ctor_set_uint8(v_reuseFailAlloc_2181_, sizeof(void*)*1, v_hasTrace_2168_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2183_, lean_object* v_k_2184_, lean_object* v_v_2185_){
_start:
{
uint8_t v_v_boxed_2186_; lean_object* v_res_2187_; 
v_v_boxed_2186_ = lean_unbox(v_v_2185_);
v_res_2187_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2183_, v_k_2184_, v_v_boxed_2186_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2188_, lean_object* v_opt_2189_, uint8_t v_val_2190_){
_start:
{
lean_object* v_name_2191_; lean_object* v___x_2192_; 
v_name_2191_ = lean_ctor_get(v_opt_2189_, 0);
lean_inc(v_name_2191_);
lean_dec_ref(v_opt_2189_);
v___x_2192_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2188_, v_name_2191_, v_val_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2193_, lean_object* v_opt_2194_, lean_object* v_val_2195_){
_start:
{
uint8_t v_val_boxed_2196_; lean_object* v_res_2197_; 
v_val_boxed_2196_ = lean_unbox(v_val_2195_);
v_res_2197_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2193_, v_opt_2194_, v_val_boxed_2196_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2198_, lean_object* v_opt_2199_, uint8_t v_val_2200_){
_start:
{
lean_object* v_name_2201_; lean_object* v_map_2202_; uint8_t v___x_2203_; 
v_name_2201_ = lean_ctor_get(v_opt_2199_, 0);
v_map_2202_ = lean_ctor_get(v_opts_2198_, 0);
v___x_2203_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2201_, v_map_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2198_, v_opt_2199_, v_val_2200_);
return v___x_2204_;
}
else
{
lean_dec_ref(v_opt_2199_);
return v_opts_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2205_, lean_object* v_opt_2206_, lean_object* v_val_2207_){
_start:
{
uint8_t v_val_boxed_2208_; lean_object* v_res_2209_; 
v_val_boxed_2208_ = lean_unbox(v_val_2207_);
v_res_2209_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2205_, v_opt_2206_, v_val_boxed_2208_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2210_, size_t v_i_2211_, lean_object* v_bs_2212_){
_start:
{
uint8_t v___x_2213_; 
v___x_2213_ = lean_usize_dec_lt(v_i_2211_, v_sz_2210_);
if (v___x_2213_ == 0)
{
return v_bs_2212_;
}
else
{
lean_object* v_v_2214_; lean_object* v_traces_2215_; lean_object* v___x_2216_; lean_object* v_bs_x27_2217_; size_t v___x_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v_v_2214_ = lean_array_uget_borrowed(v_bs_2212_, v_i_2211_);
v_traces_2215_ = lean_ctor_get(v_v_2214_, 3);
lean_inc_ref(v_traces_2215_);
v___x_2216_ = lean_unsigned_to_nat(0u);
v_bs_x27_2217_ = lean_array_uset(v_bs_2212_, v_i_2211_, v___x_2216_);
v___x_2218_ = ((size_t)1ULL);
v___x_2219_ = lean_usize_add(v_i_2211_, v___x_2218_);
v___x_2220_ = lean_array_uset(v_bs_x27_2217_, v_i_2211_, v_traces_2215_);
v_i_2211_ = v___x_2219_;
v_bs_2212_ = v___x_2220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2222_, lean_object* v_i_2223_, lean_object* v_bs_2224_){
_start:
{
size_t v_sz_boxed_2225_; size_t v_i_boxed_2226_; lean_object* v_res_2227_; 
v_sz_boxed_2225_ = lean_unbox_usize(v_sz_2222_);
lean_dec(v_sz_2222_);
v_i_boxed_2226_ = lean_unbox_usize(v_i_2223_);
lean_dec(v_i_2223_);
v_res_2227_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2225_, v_i_boxed_2226_, v_bs_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = l_Lean_Language_Snapshot_transform(v_s_2230_, v___y_2231_);
v___x_2233_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2235_, v___y_2236_);
lean_dec_ref(v___y_2236_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___f_2241_; lean_object* v___x_2242_; 
v___f_2241_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2242_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2239_, v___f_2241_, v_a_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2243_, v_a_2244_);
lean_dec_ref(v_a_2244_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2250_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2247_, v___x_2249_, v_a_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2251_, v_a_2252_);
lean_dec_ref(v_a_2252_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_toSnapshot_2256_; lean_object* v_metaSnap_2257_; lean_object* v_result_x3f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___y_2262_; 
v_toSnapshot_2256_ = lean_ctor_get(v_s_2254_, 0);
lean_inc_ref(v_toSnapshot_2256_);
v_metaSnap_2257_ = lean_ctor_get(v_s_2254_, 1);
lean_inc_ref(v_metaSnap_2257_);
v_result_x3f_2258_ = lean_ctor_get(v_s_2254_, 2);
lean_inc(v_result_x3f_2258_);
lean_dec_ref(v_s_2254_);
v___x_2259_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2256_, v___y_2255_);
v___x_2260_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2257_, v___y_2255_);
if (lean_obj_tag(v_result_x3f_2258_) == 0)
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_box(0);
v___y_2262_ = v___x_2268_;
goto v___jp_2261_;
}
else
{
lean_object* v_val_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2278_; 
v_val_2269_ = lean_ctor_get(v_result_x3f_2258_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_result_x3f_2258_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2271_ = v_result_x3f_2258_;
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_val_2269_);
lean_dec(v_result_x3f_2258_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2278_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v_firstCmdSnap_2273_; lean_object* v___x_2274_; lean_object* v___x_2276_; 
v_firstCmdSnap_2273_ = lean_ctor_get(v_val_2269_, 1);
lean_inc_ref(v_firstCmdSnap_2273_);
lean_dec(v_val_2269_);
v___x_2274_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2273_, v___y_2255_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2274_);
v___x_2276_ = v___x_2271_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
v___y_2262_ = v___x_2276_;
goto v___jp_2261_;
}
}
}
v___jp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_mk_empty_array_with_capacity(v___x_2263_);
v___x_2265_ = lean_array_push(v___x_2264_, v___x_2260_);
v___x_2266_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2262_, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2259_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2279_, v___y_2280_);
lean_dec_ref(v___y_2280_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___f_2285_; lean_object* v___x_2286_; 
v___f_2285_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2286_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2283_, v___f_2285_, v_a_2284_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2287_, v_a_2288_);
lean_dec_ref(v_a_2288_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2290_){
_start:
{
lean_object* v_toSnapshot_2291_; lean_object* v_metaSnap_2292_; lean_object* v_result_x3f_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___y_2298_; 
v_toSnapshot_2291_ = lean_ctor_get(v_a_2290_, 0);
lean_inc_ref(v_toSnapshot_2291_);
v_metaSnap_2292_ = lean_ctor_get(v_a_2290_, 1);
lean_inc_ref(v_metaSnap_2292_);
v_result_x3f_2293_ = lean_ctor_get(v_a_2290_, 4);
lean_inc(v_result_x3f_2293_);
lean_dec_ref(v_a_2290_);
v___x_2294_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2295_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2291_, v___x_2294_);
v___x_2296_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2292_, v___x_2294_);
if (lean_obj_tag(v_result_x3f_2293_) == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_box(0);
v___y_2298_ = v___x_2304_;
goto v___jp_2297_;
}
else
{
lean_object* v_val_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2314_; 
v_val_2305_ = lean_ctor_get(v_result_x3f_2293_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_result_x3f_2293_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2307_ = v_result_x3f_2293_;
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_val_2305_);
lean_dec(v_result_x3f_2293_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2314_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_processedSnap_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v_processedSnap_2309_ = lean_ctor_get(v_val_2305_, 1);
lean_inc_ref(v_processedSnap_2309_);
lean_dec(v_val_2305_);
v___x_2310_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2309_, v___x_2294_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2310_);
v___x_2312_ = v___x_2307_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
v___y_2298_ = v___x_2312_;
goto v___jp_2297_;
}
}
}
v___jp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
v___x_2301_ = lean_array_push(v___x_2300_, v___x_2296_);
v___x_2302_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2298_, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2295_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_as_2315_, size_t v_i_2316_, size_t v_stop_2317_, lean_object* v_b_2318_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_eq(v_i_2316_, v_stop_2317_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; size_t v___x_2324_; size_t v___x_2325_; 
v___x_2320_ = lean_array_uget_borrowed(v_as_2315_, v_i_2316_);
v___x_2321_ = 2;
v___x_2322_ = lean_box(v___x_2321_);
lean_inc(v___x_2320_);
v___x_2323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2320_, v___x_2322_, v_b_2318_);
v___x_2324_ = ((size_t)1ULL);
v___x_2325_ = lean_usize_add(v_i_2316_, v___x_2324_);
v_i_2316_ = v___x_2325_;
v_b_2318_ = v___x_2323_;
goto _start;
}
else
{
return v_b_2318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8___boxed(lean_object* v_as_2327_, lean_object* v_i_2328_, lean_object* v_stop_2329_, lean_object* v_b_2330_){
_start:
{
size_t v_i_boxed_2331_; size_t v_stop_boxed_2332_; lean_object* v_res_2333_; 
v_i_boxed_2331_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_stop_boxed_2332_ = lean_unbox_usize(v_stop_2329_);
lean_dec(v_stop_2329_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_as_2327_, v_i_boxed_2331_, v_stop_boxed_2332_, v_b_2330_);
lean_dec_ref(v_as_2327_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2334_, size_t v_i_2335_, size_t v_stop_2336_, lean_object* v_b_2337_){
_start:
{
lean_object* v___y_2339_; uint8_t v___x_2343_; 
v___x_2343_ = lean_usize_dec_eq(v_i_2335_, v_stop_2336_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v_infoTree_x3f_2345_; 
v___x_2344_ = lean_array_uget_borrowed(v_as_2334_, v_i_2335_);
v_infoTree_x3f_2345_ = lean_ctor_get(v___x_2344_, 2);
if (lean_obj_tag(v_infoTree_x3f_2345_) == 1)
{
lean_object* v_val_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_val_2346_ = lean_ctor_get(v_infoTree_x3f_2345_, 0);
v___x_2347_ = lean_unsigned_to_nat(1u);
v___x_2348_ = lean_mk_empty_array_with_capacity(v___x_2347_);
lean_inc(v_val_2346_);
v___x_2349_ = lean_array_push(v___x_2348_, v_val_2346_);
v___x_2350_ = l_Array_append___redArg(v_b_2337_, v___x_2349_);
lean_dec_ref(v___x_2349_);
v___y_2339_ = v___x_2350_;
goto v___jp_2338_;
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2352_ = l_Array_append___redArg(v_b_2337_, v___x_2351_);
v___y_2339_ = v___x_2352_;
goto v___jp_2338_;
}
}
else
{
return v_b_2337_;
}
v___jp_2338_:
{
size_t v___x_2340_; size_t v___x_2341_; 
v___x_2340_ = ((size_t)1ULL);
v___x_2341_ = lean_usize_add(v_i_2335_, v___x_2340_);
v_i_2335_ = v___x_2341_;
v_b_2337_ = v___y_2339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2353_, lean_object* v_i_2354_, lean_object* v_stop_2355_, lean_object* v_b_2356_){
_start:
{
size_t v_i_boxed_2357_; size_t v_stop_boxed_2358_; lean_object* v_res_2359_; 
v_i_boxed_2357_ = lean_unbox_usize(v_i_2354_);
lean_dec(v_i_2354_);
v_stop_boxed_2358_ = lean_unbox_usize(v_stop_2355_);
lean_dec(v_stop_2355_);
v_res_2359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2353_, v_i_boxed_2357_, v_stop_boxed_2358_, v_b_2356_);
lean_dec_ref(v_as_2353_);
return v_res_2359_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__1(void){
_start:
{
lean_object* v___x_2361_; double v___x_2362_; 
v___x_2361_ = lean_unsigned_to_nat(1000000000u);
v___x_2362_ = lean_float_of_nat(v___x_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2364_, lean_object* v_opts_2365_, lean_object* v_fileName_2366_, lean_object* v_mainModuleName_2367_, uint32_t v_trustLevel_2368_, lean_object* v_oleanFileName_x3f_2369_, lean_object* v_ileanFileName_x3f_2370_, uint8_t v_jsonOutput_2371_, lean_object* v_errorOnKinds_2372_, lean_object* v_plugins_2373_, uint8_t v_printStats_2374_, lean_object* v_setup_x3f_2375_, lean_object* v_incrSaveFileName_x3f_2376_, lean_object* v_incrLoadFileName_x3f_2377_, lean_object* v_incrHeaderSaveFileName_x3f_2378_){
_start:
{
lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___x_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; double v___x_2389_; double v___x_2390_; double v___x_2391_; uint8_t v___x_2392_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___y_2460_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; uint8_t v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; uint8_t v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; uint8_t v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; uint8_t v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; uint8_t v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v_a_2639_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v___y_2660_; 
v___x_2386_ = lean_io_mono_nanos_now();
v___f_2387_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_2388_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2389_ = lean_float_of_nat(v___x_2386_);
v___x_2390_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__1, &l_Lean_Elab_runFrontend___closed__1_once, _init_l_Lean_Elab_runFrontend___closed__1);
v___x_2391_ = lean_float_div(v___x_2389_, v___x_2390_);
v___x_2392_ = 1;
v___x_2455_ = lean_string_utf8_byte_size(v_input_2364_);
v___x_2456_ = l_Lean_Parser_mkInputContext___redArg(v_input_2364_, v_fileName_2366_, v___x_2392_, v___x_2455_);
v___x_2658_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2376_) == 0)
{
v___y_2660_ = v___x_2392_;
goto v___jp_2659_;
}
else
{
uint8_t v___x_2696_; 
v___x_2696_ = 0;
v___y_2660_ = v___x_2696_;
goto v___jp_2659_;
}
v___jp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = lean_runtime_forget(v___y_2382_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___y_2381_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
v___jp_2393_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = l_Lean_trace_profiler_output;
v___x_2399_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2394_, v___x_2398_);
if (lean_obj_tag(v___x_2399_) == 1)
{
lean_object* v_val_2400_; lean_object* v___x_2401_; size_t v_sz_2402_; size_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
lean_dec_ref(v___y_2396_);
v_val_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v___x_2399_, 1);
lean_inc_ref(v___y_2397_);
v___x_2401_ = l_Lean_Language_SnapshotTree_getAll(v___y_2397_);
v_sz_2402_ = lean_array_size(v___x_2401_);
v___x_2403_ = ((size_t)0ULL);
v___x_2404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2402_, v___x_2403_, v___x_2401_);
v___x_2405_ = l_Lean_Name_toString(v_mainModuleName_2367_, v___x_2392_);
v___x_2406_ = l_Lean_Firefox_Profile_export(v___x_2405_, v___x_2391_, v___x_2404_, v___y_2394_);
lean_dec_ref(v___y_2394_);
lean_dec_ref(v___x_2404_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2408_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2407_);
v___x_2409_ = l_Lean_Json_compress(v___x_2408_);
v___x_2410_ = l_IO_FS_writeFile(v_val_2400_, v___x_2409_);
lean_dec_ref(v___x_2409_);
lean_dec(v_val_2400_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_dec_ref_known(v___x_2410_, 1);
v___y_2381_ = v___y_2395_;
v___y_2382_ = v___y_2397_;
goto v___jp_2380_;
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec_ref(v___y_2397_);
lean_dec_ref(v___y_2395_);
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2410_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_val_2400_);
lean_dec_ref(v___y_2397_);
lean_dec_ref(v___y_2395_);
v_a_2419_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2406_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2406_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
lean_dec(v___x_2399_);
v___x_2427_ = l_Lean_trace_profiler_serve;
v___x_2428_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2396_, v___x_2427_);
lean_dec_ref(v___y_2396_);
if (v___x_2428_ == 0)
{
lean_dec_ref(v___y_2394_);
lean_dec(v_mainModuleName_2367_);
v___y_2381_ = v___y_2395_;
v___y_2382_ = v___y_2397_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2429_; size_t v_sz_2430_; size_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_inc_ref(v___y_2397_);
v___x_2429_ = l_Lean_Language_SnapshotTree_getAll(v___y_2397_);
v_sz_2430_ = lean_array_size(v___x_2429_);
v___x_2431_ = ((size_t)0ULL);
v___x_2432_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2430_, v___x_2431_, v___x_2429_);
v___x_2433_ = l_Lean_Name_toString(v_mainModuleName_2367_, v___x_2392_);
v___x_2434_ = l_Lean_Firefox_Profile_export(v___x_2433_, v___x_2391_, v___x_2432_, v___y_2394_);
lean_dec_ref(v___y_2394_);
lean_dec_ref(v___x_2432_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v___x_2434_, 1);
v___x_2436_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2435_);
v___x_2437_ = l_Lean_Json_compress(v___x_2436_);
v___x_2438_ = l_Lean_Firefox_Profile_serve(v___x_2437_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_dec_ref_known(v___x_2438_, 1);
v___y_2381_ = v___y_2395_;
v___y_2382_ = v___y_2397_;
goto v___jp_2380_;
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
lean_dec_ref(v___y_2397_);
lean_dec_ref(v___y_2395_);
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
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
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
lean_dec_ref(v___y_2397_);
lean_dec_ref(v___y_2395_);
v_a_2447_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2434_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2434_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
}
v___jp_2457_:
{
lean_object* v_fileMap_2465_; uint8_t v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v_stx_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2491_; 
v_fileMap_2465_ = lean_ctor_get(v___x_2456_, 2);
lean_inc_ref(v_fileMap_2465_);
lean_dec_ref(v___x_2456_);
v___x_2466_ = 0;
v___x_2467_ = l_Lean_Server_findModuleRefs(v_fileMap_2465_, v___y_2464_, v___x_2466_, v___x_2466_);
lean_dec_ref(v___y_2464_);
v___x_2468_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2467_);
v_fst_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_fst_2469_);
v_snd_2470_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_snd_2470_);
lean_dec_ref(v___x_2468_);
v_stx_2471_ = lean_ctor_get(v___y_2463_, 3);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___y_2463_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; 
v_unused_2492_ = lean_ctor_get(v___y_2463_, 4);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v___y_2463_, 2);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v___y_2463_, 1);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v___y_2463_, 0);
lean_dec(v_unused_2495_);
v___x_2473_ = v___y_2463_;
v_isShared_2474_ = v_isSharedCheck_2491_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_stx_2471_);
lean_dec(v___y_2463_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2491_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2475_ = lean_unsigned_to_nat(5u);
v___x_2476_ = l_Lean_Server_collectImports(v_stx_2471_);
lean_inc(v_mainModuleName_2367_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 4, v_snd_2470_);
lean_ctor_set(v___x_2473_, 3, v_fst_2469_);
lean_ctor_set(v___x_2473_, 2, v___x_2476_);
lean_ctor_set(v___x_2473_, 1, v_mainModuleName_2367_);
lean_ctor_set(v___x_2473_, 0, v___x_2475_);
v___x_2478_ = v___x_2473_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_mainModuleName_2367_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_fst_2469_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_snd_2470_);
v___x_2478_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2478_);
v___x_2480_ = l_Lean_Json_compress(v___x_2479_);
v___x_2481_ = l_IO_FS_writeFile(v___y_2459_, v___x_2480_);
lean_dec_ref(v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_dec_ref_known(v___x_2481_, 1);
v___y_2394_ = v___y_2458_;
v___y_2395_ = v___y_2460_;
v___y_2396_ = v___y_2461_;
v___y_2397_ = v___y_2462_;
goto v___jp_2393_;
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec_ref(v___y_2458_);
lean_dec(v_mainModuleName_2367_);
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
v___jp_2496_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2370_) == 1)
{
lean_object* v_val_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_val_2503_ = lean_ctor_get(v_ileanFileName_x3f_2370_, 0);
lean_inc_ref(v___y_2501_);
v___x_2504_ = l_Lean_Language_SnapshotTree_getAll(v___y_2501_);
v___x_2505_ = lean_mk_empty_array_with_capacity(v___y_2498_);
v___x_2506_ = lean_array_get_size(v___x_2504_);
v___x_2507_ = lean_nat_dec_lt(v___y_2498_, v___x_2506_);
lean_dec(v___y_2498_);
if (v___x_2507_ == 0)
{
lean_dec_ref(v___x_2504_);
v___y_2458_ = v___y_2497_;
v___y_2459_ = v_val_2503_;
v___y_2460_ = v___y_2499_;
v___y_2461_ = v___y_2500_;
v___y_2462_ = v___y_2501_;
v___y_2463_ = v___y_2502_;
v___y_2464_ = v___x_2505_;
goto v___jp_2457_;
}
else
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_nat_dec_le(v___x_2506_, v___x_2506_);
if (v___x_2508_ == 0)
{
if (v___x_2507_ == 0)
{
lean_dec_ref(v___x_2504_);
v___y_2458_ = v___y_2497_;
v___y_2459_ = v_val_2503_;
v___y_2460_ = v___y_2499_;
v___y_2461_ = v___y_2500_;
v___y_2462_ = v___y_2501_;
v___y_2463_ = v___y_2502_;
v___y_2464_ = v___x_2505_;
goto v___jp_2457_;
}
else
{
size_t v___x_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = ((size_t)0ULL);
v___x_2510_ = lean_usize_of_nat(v___x_2506_);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2504_, v___x_2509_, v___x_2510_, v___x_2505_);
lean_dec_ref(v___x_2504_);
v___y_2458_ = v___y_2497_;
v___y_2459_ = v_val_2503_;
v___y_2460_ = v___y_2499_;
v___y_2461_ = v___y_2500_;
v___y_2462_ = v___y_2501_;
v___y_2463_ = v___y_2502_;
v___y_2464_ = v___x_2511_;
goto v___jp_2457_;
}
}
else
{
size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((size_t)0ULL);
v___x_2513_ = lean_usize_of_nat(v___x_2506_);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2504_, v___x_2512_, v___x_2513_, v___x_2505_);
lean_dec_ref(v___x_2504_);
v___y_2458_ = v___y_2497_;
v___y_2459_ = v_val_2503_;
v___y_2460_ = v___y_2499_;
v___y_2461_ = v___y_2500_;
v___y_2462_ = v___y_2501_;
v___y_2463_ = v___y_2502_;
v___y_2464_ = v___x_2514_;
goto v___jp_2457_;
}
}
}
else
{
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2498_);
lean_dec_ref(v___x_2456_);
v___y_2394_ = v___y_2497_;
v___y_2395_ = v___y_2499_;
v___y_2396_ = v___y_2500_;
v___y_2397_ = v___y_2501_;
goto v___jp_2393_;
}
}
v___jp_2515_:
{
if (v___y_2519_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2369_) == 1)
{
lean_object* v_val_2526_; lean_object* v_fileMap_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_val_2526_ = lean_ctor_get(v_oleanFileName_x3f_2369_, 0);
lean_inc(v_val_2526_);
lean_dec_ref_known(v_oleanFileName_x3f_2369_, 1);
v_fileMap_2527_ = lean_ctor_get(v___x_2456_, 2);
lean_inc_ref(v_fileMap_2527_);
v___x_2528_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__2));
v___x_2529_ = lean_box(0);
v___x_2530_ = lean_mk_empty_array_with_capacity(v___y_2521_);
lean_inc_ref(v___y_2524_);
v___x_2531_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2524_, v___x_2529_, v___x_2530_);
v___x_2532_ = lean_box(v___x_2392_);
v___x_2533_ = lean_box(v___y_2516_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2534_, 0, v_fileMap_2527_);
lean_closure_set(v___f_2534_, 1, v___y_2517_);
lean_closure_set(v___f_2534_, 2, v___x_2531_);
lean_closure_set(v___f_2534_, 3, v___y_2518_);
lean_closure_set(v___f_2534_, 4, v_val_2526_);
lean_closure_set(v___f_2534_, 5, v___x_2532_);
lean_closure_set(v___f_2534_, 6, v___x_2533_);
v___x_2535_ = lean_box(0);
v___x_2536_ = l_Lean_profileitIOUnsafe___redArg(v___x_2528_, v___y_2522_, v___f_2534_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_dec_ref_known(v___x_2536_, 1);
v___y_2497_ = v___y_2520_;
v___y_2498_ = v___y_2521_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2522_;
v___y_2501_ = v___y_2524_;
v___y_2502_ = v___y_2525_;
goto v___jp_2496_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec_ref(v___x_2456_);
lean_dec(v_mainModuleName_2367_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v_oleanFileName_x3f_2369_);
v___y_2497_ = v___y_2520_;
v___y_2498_ = v___y_2521_;
v___y_2499_ = v___y_2523_;
v___y_2500_ = v___y_2522_;
v___y_2501_ = v___y_2524_;
v___y_2502_ = v___y_2525_;
goto v___jp_2496_;
}
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec_ref(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___x_2456_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
return v___x_2546_;
}
}
v___jp_2547_:
{
if (v_printStats_2374_ == 0)
{
v___y_2516_ = v___y_2548_;
v___y_2517_ = v___y_2549_;
v___y_2518_ = v___y_2550_;
v___y_2519_ = v___y_2551_;
v___y_2520_ = v___y_2552_;
v___y_2521_ = v___y_2553_;
v___y_2522_ = v___y_2554_;
v___y_2523_ = v___y_2555_;
v___y_2524_ = v___y_2556_;
v___y_2525_ = v___y_2557_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2558_; 
lean_inc_ref(v___y_2555_);
v___x_2558_ = l_Lean_Environment_displayStats(v___y_2555_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_dec_ref_known(v___x_2558_, 1);
v___y_2516_ = v___y_2548_;
v___y_2517_ = v___y_2549_;
v___y_2518_ = v___y_2550_;
v___y_2519_ = v___y_2551_;
v___y_2520_ = v___y_2552_;
v___y_2521_ = v___y_2553_;
v___y_2522_ = v___y_2554_;
v___y_2523_ = v___y_2555_;
v___y_2524_ = v___y_2556_;
v___y_2525_ = v___y_2557_;
goto v___jp_2515_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec_ref(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec_ref(v___x_2456_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
v___jp_2567_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2378_) == 1)
{
lean_object* v_val_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_val_2578_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2378_, 0);
lean_inc(v_val_2578_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2378_, 1);
lean_inc_ref(v___y_2577_);
v___x_2579_ = l_Lean_Language_Lean_truncateToHeader(v___y_2577_);
v___x_2580_ = lean_apply_3(v___y_2571_, v_val_2578_, v___x_2579_, lean_box(0));
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_dec_ref_known(v___x_2580_, 1);
lean_inc_ref(v___y_2569_);
v___y_2548_ = v___y_2568_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2569_;
v___y_2551_ = v___y_2572_;
v___y_2552_ = v___y_2573_;
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___y_2569_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2576_;
v___y_2557_ = v___y_2577_;
goto v___jp_2547_;
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec_ref(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec_ref(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___x_2456_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_dec_ref(v___y_2571_);
lean_dec(v_incrHeaderSaveFileName_x3f_2378_);
lean_inc_ref(v___y_2569_);
v___y_2548_ = v___y_2568_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2569_;
v___y_2551_ = v___y_2572_;
v___y_2552_ = v___y_2573_;
v___y_2553_ = v___y_2574_;
v___y_2554_ = v___y_2569_;
v___y_2555_ = v___y_2575_;
v___y_2556_ = v___y_2576_;
v___y_2557_ = v___y_2577_;
goto v___jp_2547_;
}
}
v___jp_2589_:
{
lean_object* v___x_2595_; 
lean_inc_ref(v___y_2592_);
v___x_2595_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2592_, v___y_2590_, v_jsonOutput_2371_, v___y_2594_);
lean_dec(v___y_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2627_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2627_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2627_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; 
lean_inc_ref(v___y_2593_);
v___x_2600_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2593_);
if (lean_obj_tag(v___x_2600_) == 1)
{
lean_object* v_val_2601_; lean_object* v_env_2602_; lean_object* v_scopes_2603_; lean_object* v___x_2604_; lean_object* v_opts_2605_; lean_object* v___x_2606_; lean_object* v___f_2607_; 
lean_del_object(v___x_2598_);
v_val_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_val_2601_);
lean_dec_ref_known(v___x_2600_, 1);
v_env_2602_ = lean_ctor_get(v_val_2601_, 0);
lean_inc_ref_n(v_env_2602_, 2);
v_scopes_2603_ = lean_ctor_get(v_val_2601_, 2);
lean_inc(v_scopes_2603_);
lean_dec(v_val_2601_);
lean_inc(v___y_2591_);
v___x_2604_ = l_List_get_x21Internal___redArg(v___x_2388_, v_scopes_2603_, v___y_2591_);
lean_dec(v_scopes_2603_);
v_opts_2605_ = lean_ctor_get(v___x_2604_, 1);
lean_inc_ref(v_opts_2605_);
lean_dec(v___x_2604_);
v___x_2606_ = lean_box(v___x_2392_);
v___f_2607_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2607_, 0, v_env_2602_);
lean_closure_set(v___f_2607_, 1, v___x_2606_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2376_) == 1)
{
lean_object* v_val_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_val_2608_ = lean_ctor_get(v_incrSaveFileName_x3f_2376_, 0);
lean_inc(v_val_2608_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2376_, 1);
v___x_2609_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2592_);
lean_inc_ref(v___y_2593_);
v___x_2610_ = l_Lean_Elab_runFrontend___lam__1(v_env_2602_, v___x_2392_, v_val_2608_, v___y_2593_);
if (lean_obj_tag(v___x_2610_) == 0)
{
uint8_t v___x_2611_; uint8_t v___x_2612_; 
lean_dec_ref_known(v___x_2610_, 1);
v___x_2611_ = lean_unbox(v_a_2596_);
v___x_2612_ = lean_unbox(v_a_2596_);
lean_dec(v_a_2596_);
lean_inc_ref(v_env_2602_);
v___y_2568_ = v___x_2611_;
v___y_2569_ = v_opts_2605_;
v___y_2570_ = v_env_2602_;
v___y_2571_ = v___f_2607_;
v___y_2572_ = v___x_2612_;
v___y_2573_ = v___y_2590_;
v___y_2574_ = v___y_2591_;
v___y_2575_ = v_env_2602_;
v___y_2576_ = v___y_2592_;
v___y_2577_ = v___y_2593_;
goto v___jp_2567_;
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec_ref(v___f_2607_);
lean_dec_ref(v_opts_2605_);
lean_dec_ref(v_env_2602_);
lean_dec(v_a_2596_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___x_2456_);
lean_dec(v_incrHeaderSaveFileName_x3f_2378_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v_a_2613_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2610_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2610_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
uint8_t v___x_2621_; uint8_t v___x_2622_; 
lean_dec(v_incrSaveFileName_x3f_2376_);
v___x_2621_ = lean_unbox(v_a_2596_);
v___x_2622_ = lean_unbox(v_a_2596_);
lean_dec(v_a_2596_);
lean_inc_ref(v_env_2602_);
v___y_2568_ = v___x_2621_;
v___y_2569_ = v_opts_2605_;
v___y_2570_ = v_env_2602_;
v___y_2571_ = v___f_2607_;
v___y_2572_ = v___x_2622_;
v___y_2573_ = v___y_2590_;
v___y_2574_ = v___y_2591_;
v___y_2575_ = v_env_2602_;
v___y_2576_ = v___y_2592_;
v___y_2577_ = v___y_2593_;
goto v___jp_2567_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_dec(v___x_2600_);
lean_dec(v_a_2596_);
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___x_2456_);
lean_dec(v_incrHeaderSaveFileName_x3f_2378_);
lean_dec(v_incrSaveFileName_x3f_2376_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v___x_2623_ = lean_box(0);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2623_);
v___x_2625_ = v___x_2598_;
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
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec_ref(v___x_2456_);
lean_dec(v_incrHeaderSaveFileName_x3f_2378_);
lean_dec(v_incrSaveFileName_x3f_2376_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v_a_2628_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2595_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2595_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
v___jp_2636_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2640_ = l_Lean_Language_Lean_process(v___y_2638_, v_a_2639_, v___x_2456_);
lean_inc_ref(v___x_2640_);
v___x_2641_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2640_);
v___x_2642_ = lean_box(1);
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_array_get_size(v_errorOnKinds_2372_);
v___x_2645_ = lean_nat_dec_lt(v___x_2643_, v___x_2644_);
if (v___x_2645_ == 0)
{
v___y_2590_ = v___y_2637_;
v___y_2591_ = v___x_2643_;
v___y_2592_ = v___x_2641_;
v___y_2593_ = v___x_2640_;
v___y_2594_ = v___x_2642_;
goto v___jp_2589_;
}
else
{
uint8_t v___x_2646_; 
v___x_2646_ = lean_nat_dec_le(v___x_2644_, v___x_2644_);
if (v___x_2646_ == 0)
{
if (v___x_2645_ == 0)
{
v___y_2590_ = v___y_2637_;
v___y_2591_ = v___x_2643_;
v___y_2592_ = v___x_2641_;
v___y_2593_ = v___x_2640_;
v___y_2594_ = v___x_2642_;
goto v___jp_2589_;
}
else
{
size_t v___x_2647_; size_t v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = ((size_t)0ULL);
v___x_2648_ = lean_usize_of_nat(v___x_2644_);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_errorOnKinds_2372_, v___x_2647_, v___x_2648_, v___x_2642_);
v___y_2590_ = v___y_2637_;
v___y_2591_ = v___x_2643_;
v___y_2592_ = v___x_2641_;
v___y_2593_ = v___x_2640_;
v___y_2594_ = v___x_2649_;
goto v___jp_2589_;
}
}
else
{
size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = ((size_t)0ULL);
v___x_2651_ = lean_usize_of_nat(v___x_2644_);
v___x_2652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_errorOnKinds_2372_, v___x_2650_, v___x_2651_, v___x_2642_);
v___y_2590_ = v___y_2637_;
v___y_2591_ = v___x_2643_;
v___y_2592_ = v___x_2641_;
v___y_2593_ = v___x_2640_;
v___y_2594_ = v___x_2652_;
goto v___jp_2589_;
}
}
}
v___jp_2653_:
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_a_2656_);
v___y_2637_ = v___y_2654_;
v___y_2638_ = v___y_2655_;
v_a_2639_ = v___x_2657_;
goto v___jp_2636_;
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___f_2666_; 
v___x_2661_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2365_, v___x_2658_, v___y_2660_);
v___x_2662_ = l_Lean_Elab_async;
v___x_2663_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2661_, v___x_2662_, v___x_2392_);
v___x_2664_ = lean_box_uint32(v_trustLevel_2368_);
v___x_2665_ = lean_box(v___x_2392_);
lean_inc(v_mainModuleName_2367_);
lean_inc_ref(v___x_2663_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 10, 7);
lean_closure_set(v___f_2666_, 0, v_setup_x3f_2375_);
lean_closure_set(v___f_2666_, 1, v___f_2387_);
lean_closure_set(v___f_2666_, 2, v___x_2663_);
lean_closure_set(v___f_2666_, 3, v_plugins_2373_);
lean_closure_set(v___f_2666_, 4, v___x_2664_);
lean_closure_set(v___f_2666_, 5, v___x_2665_);
lean_closure_set(v___f_2666_, 6, v_mainModuleName_2367_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2377_) == 0)
{
lean_object* v___x_2667_; 
v___x_2667_ = lean_box(0);
v___y_2637_ = v___x_2663_;
v___y_2638_ = v___f_2666_;
v_a_2639_ = v___x_2667_;
goto v___jp_2636_;
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2669_; 
v_val_2668_ = lean_ctor_get(v_incrLoadFileName_x3f_2377_, 0);
lean_inc(v_val_2668_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2377_, 1);
v___x_2669_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2668_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v_snap_2671_; lean_object* v_initModIdxs_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v_snap_2671_ = lean_ctor_get(v_a_2670_, 0);
lean_inc_ref(v_snap_2671_);
v_initModIdxs_2672_ = lean_ctor_get(v_a_2670_, 1);
lean_inc_ref(v_initModIdxs_2672_);
lean_dec(v_a_2670_);
lean_inc(v_mainModuleName_2367_);
v___x_2673_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2671_, v_mainModuleName_2367_);
lean_inc_ref(v___x_2673_);
v___x_2674_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2673_);
v___x_2675_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2674_);
if (lean_obj_tag(v___x_2675_) == 1)
{
lean_object* v_val_2676_; lean_object* v___f_2677_; lean_object* v___x_2678_; 
v_val_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_val_2676_);
lean_dec_ref_known(v___x_2675_, 1);
lean_inc_ref(v___x_2663_);
v___f_2677_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2677_, 0, v_val_2676_);
lean_closure_set(v___f_2677_, 1, v_initModIdxs_2672_);
lean_closure_set(v___f_2677_, 2, v___x_2663_);
v___x_2678_ = l_Lean_withImporting___redArg(v___f_2677_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2679_; 
lean_dec_ref_known(v___x_2678_, 1);
v___x_2679_ = lean_enable_initializer_execution();
v___y_2654_ = v___x_2663_;
v___y_2655_ = v___f_2666_;
v_a_2656_ = v___x_2673_;
goto v___jp_2653_;
}
else
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2687_; 
lean_dec_ref(v___x_2673_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___x_2663_);
lean_dec_ref(v___x_2456_);
lean_dec(v_incrHeaderSaveFileName_x3f_2378_);
lean_dec(v_incrSaveFileName_x3f_2376_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v_a_2680_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2682_ = v___x_2678_;
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2678_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2687_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2685_; 
if (v_isShared_2683_ == 0)
{
v___x_2685_ = v___x_2682_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v_a_2680_);
v___x_2685_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
return v___x_2685_;
}
}
}
}
else
{
lean_dec(v___x_2675_);
lean_dec_ref(v_initModIdxs_2672_);
v___y_2654_ = v___x_2663_;
v___y_2655_ = v___f_2666_;
v_a_2656_ = v___x_2673_;
goto v___jp_2653_;
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___x_2663_);
lean_dec_ref(v___x_2456_);
lean_dec(v_incrHeaderSaveFileName_x3f_2378_);
lean_dec(v_incrSaveFileName_x3f_2376_);
lean_dec(v_oleanFileName_x3f_2369_);
lean_dec(v_mainModuleName_2367_);
v_a_2688_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2669_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2669_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2697_, lean_object* v_opts_2698_, lean_object* v_fileName_2699_, lean_object* v_mainModuleName_2700_, lean_object* v_trustLevel_2701_, lean_object* v_oleanFileName_x3f_2702_, lean_object* v_ileanFileName_x3f_2703_, lean_object* v_jsonOutput_2704_, lean_object* v_errorOnKinds_2705_, lean_object* v_plugins_2706_, lean_object* v_printStats_2707_, lean_object* v_setup_x3f_2708_, lean_object* v_incrSaveFileName_x3f_2709_, lean_object* v_incrLoadFileName_x3f_2710_, lean_object* v_incrHeaderSaveFileName_x3f_2711_, lean_object* v_a_2712_){
_start:
{
uint32_t v_trustLevel_boxed_2713_; uint8_t v_jsonOutput_boxed_2714_; uint8_t v_printStats_boxed_2715_; lean_object* v_res_2716_; 
v_trustLevel_boxed_2713_ = lean_unbox_uint32(v_trustLevel_2701_);
lean_dec(v_trustLevel_2701_);
v_jsonOutput_boxed_2714_ = lean_unbox(v_jsonOutput_2704_);
v_printStats_boxed_2715_ = lean_unbox(v_printStats_2707_);
v_res_2716_ = l_Lean_Elab_runFrontend(v_input_2697_, v_opts_2698_, v_fileName_2699_, v_mainModuleName_2700_, v_trustLevel_boxed_2713_, v_oleanFileName_x3f_2702_, v_ileanFileName_x3f_2703_, v_jsonOutput_boxed_2714_, v_errorOnKinds_2705_, v_plugins_2706_, v_printStats_boxed_2715_, v_setup_x3f_2708_, v_incrSaveFileName_x3f_2709_, v_incrLoadFileName_x3f_2710_, v_incrHeaderSaveFileName_x3f_2711_);
lean_dec_ref(v_errorOnKinds_2705_);
lean_dec(v_ileanFileName_x3f_2703_);
return v_res_2716_;
}
}
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_References(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Profiler(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_ProfilerServer(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_References(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Profiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ProfilerServer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Platform(uint8_t builtin);
lean_object* initialize_Lean_Language_Lean(uint8_t builtin);
lean_object* initialize_Lean_Server_References(uint8_t builtin);
lean_object* initialize_Lean_Util_Profiler(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Linter_PersistentLintLog(uint8_t builtin);
lean_object* initialize_Lean_Util_ProfilerServer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Language_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_References(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Profiler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_PersistentLintLog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ProfilerServer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Frontend(builtin);
}
#ifdef __cplusplus
}
#endif
