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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedModuleArtifacts_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_MessageData_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_getRegularInitAttrModIdxs(lean_object*);
lean_object* lean_compacted_region_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "server"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sig"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "olean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0 = (const lean_object*)&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
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
v___x_13_ = lean_st_ref_set(v_a_2_, v___x_12_);
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
v___x_192_ = lean_st_ref_set(v_a_180_, v___x_191_);
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
v___x_253_ = lean_st_ref_set(v_a_242_, v___x_252_);
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
lean_object* v___x_276_; lean_object* v_commandState_277_; lean_object* v_parserState_278_; lean_object* v_cmdPos_279_; lean_object* v_commands_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_308_; 
v___x_276_ = lean_st_ref_take(v_a_274_);
v_commandState_277_ = lean_ctor_get(v___x_276_, 0);
v_parserState_278_ = lean_ctor_get(v___x_276_, 1);
v_cmdPos_279_ = lean_ctor_get(v___x_276_, 2);
v_commands_280_ = lean_ctor_get(v___x_276_, 3);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_308_ == 0)
{
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_308_;
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
v_isShared_283_ = v_isSharedCheck_308_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_env_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_306_; 
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
v_isSharedCheck_306_ = !lean_is_exclusive(v_commandState_277_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v_commandState_277_, 1);
lean_dec(v_unused_307_);
v___x_295_ = v_commandState_277_;
v_isShared_296_ = v_isSharedCheck_306_;
goto v_resetjp_294_;
}
else
{
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
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_306_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_msgs_273_);
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_env_284_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_msgs_273_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_305_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_305_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_305_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_305_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_305_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_305_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_305_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_305_, 10, v_snapshotTasks_293_);
v___x_298_ = v_reuseFailAlloc_305_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_298_);
v___x_300_ = v___x_282_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_parserState_278_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_cmdPos_279_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_commands_280_);
v___x_300_ = v_reuseFailAlloc_304_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_st_ref_set(v_a_274_, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* v_msgs_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_309_, v_a_310_);
lean_dec(v_a_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* v_msgs_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_313_, v_a_315_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* v_msgs_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_Frontend_setMessages(v_msgs_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; 
lean_inc_ref(v_a_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_a_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_326_);
lean_dec_ref(v_a_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; 
lean_inc_ref(v_a_329_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_a_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Elab_Frontend_getInputContext(v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_337_, lean_object* v___x_338_, lean_object* v_a_339_, lean_object* v_messages_340_, lean_object* v_x_341_){
_start:
{
lean_object* v___x_342_; 
lean_inc_ref(v_a_337_);
v___x_342_ = l_Lean_Parser_parseCommand(v_a_337_, v___x_338_, v_a_339_, v_messages_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* v_a_343_, lean_object* v___x_344_, lean_object* v_a_345_, lean_object* v_messages_346_, lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Elab_Frontend_processCommand___lam__0(v_a_343_, v___x_344_, v_a_345_, v_messages_346_, v_x_347_);
lean_dec_ref(v_a_343_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v_env_358_; lean_object* v_messages_359_; lean_object* v_scopes_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_opts_363_; lean_object* v_currNamespace_364_; lean_object* v_openDecls_365_; lean_object* v___x_366_; lean_object* v___f_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_snd_371_; lean_object* v_fst_372_; lean_object* v_fst_373_; lean_object* v_snd_374_; lean_object* v___x_375_; lean_object* v_commandState_376_; lean_object* v_parserState_377_; lean_object* v_cmdPos_378_; lean_object* v_commands_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_409_; 
v___x_353_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_351_);
lean_dec_ref(v___x_353_);
v___x_354_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_351_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v___x_356_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_351_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v___x_356_);
v_env_358_ = lean_ctor_get(v_a_355_, 0);
lean_inc_ref(v_env_358_);
v_messages_359_ = lean_ctor_get(v_a_355_, 1);
lean_inc_ref(v_messages_359_);
v_scopes_360_ = lean_ctor_get(v_a_355_, 2);
lean_inc(v_scopes_360_);
lean_dec(v_a_355_);
v___x_361_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_362_ = l_List_head_x21___redArg(v___x_361_, v_scopes_360_);
lean_dec(v_scopes_360_);
v_opts_363_ = lean_ctor_get(v___x_362_, 1);
lean_inc_ref_n(v_opts_363_, 2);
v_currNamespace_364_ = lean_ctor_get(v___x_362_, 2);
lean_inc(v_currNamespace_364_);
v_openDecls_365_ = lean_ctor_get(v___x_362_, 3);
lean_inc(v_openDecls_365_);
lean_dec(v___x_362_);
v___x_366_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_366_, 0, v_env_358_);
lean_ctor_set(v___x_366_, 1, v_opts_363_);
lean_ctor_set(v___x_366_, 2, v_currNamespace_364_);
lean_ctor_set(v___x_366_, 3, v_openDecls_365_);
lean_inc_ref(v_a_350_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_367_, 0, v_a_350_);
lean_closure_set(v___f_367_, 1, v___x_366_);
lean_closure_set(v___f_367_, 2, v_a_357_);
lean_closure_set(v___f_367_, 3, v_messages_359_);
v___x_368_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_369_ = lean_box(0);
v___x_370_ = lean_profileit(v___x_368_, v_opts_363_, v___f_367_, v___x_369_);
lean_dec_ref(v_opts_363_);
v_snd_371_ = lean_ctor_get(v___x_370_, 1);
lean_inc(v_snd_371_);
v_fst_372_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_fst_372_);
lean_dec(v___x_370_);
v_fst_373_ = lean_ctor_get(v_snd_371_, 0);
lean_inc(v_fst_373_);
v_snd_374_ = lean_ctor_get(v_snd_371_, 1);
lean_inc(v_snd_374_);
lean_dec(v_snd_371_);
v___x_375_ = lean_st_ref_take(v_a_351_);
v_commandState_376_ = lean_ctor_get(v___x_375_, 0);
v_parserState_377_ = lean_ctor_get(v___x_375_, 1);
v_cmdPos_378_ = lean_ctor_get(v___x_375_, 2);
v_commands_379_ = lean_ctor_get(v___x_375_, 3);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_409_ == 0)
{
v___x_381_ = v___x_375_;
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_commands_379_);
lean_inc(v_cmdPos_378_);
lean_inc(v_parserState_377_);
lean_inc(v_commandState_376_);
lean_dec(v___x_375_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_409_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
lean_inc(v_fst_372_);
v___x_383_ = lean_array_push(v_commands_379_, v_fst_372_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 3, v___x_383_);
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_commandState_376_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_parserState_377_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_cmdPos_378_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v___x_383_);
v___x_385_ = v_reuseFailAlloc_408_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_386_ = lean_st_ref_set(v_a_351_, v___x_385_);
v___x_387_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_373_, v_a_351_);
lean_dec_ref(v___x_387_);
v___x_388_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_374_, v_a_351_);
lean_dec_ref(v___x_388_);
lean_inc(v_fst_372_);
v___x_389_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_372_, v_a_350_, v_a_351_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_398_; 
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_398_ == 0)
{
lean_object* v_unused_399_; 
v_unused_399_ = lean_ctor_get(v___x_389_, 0);
lean_dec(v_unused_399_);
v___x_391_ = v___x_389_;
v_isShared_392_ = v_isSharedCheck_398_;
goto v_resetjp_390_;
}
else
{
lean_dec(v___x_389_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_398_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = l_Lean_Parser_isTerminalCommand(v_fst_372_);
v___x_394_ = lean_box(v___x_393_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_394_);
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
lean_dec(v_fst_372_);
v_a_400_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v___x_389_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_389_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Elab_Frontend_processCommand(v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Elab_Frontend_processCommand(v_a_414_, v_a_415_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_428_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_428_ == 0)
{
v___x_420_ = v___x_417_;
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_428_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
uint8_t v___x_422_; 
v___x_422_ = lean_unbox(v_a_418_);
lean_dec(v_a_418_);
if (v___x_422_ == 0)
{
lean_del_object(v___x_420_);
goto _start;
}
else
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_box(0);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v___x_424_);
v___x_426_ = v___x_420_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
v_a_429_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_417_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_417_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Elab_Frontend_processCommands(v_a_437_, v_a_438_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(lean_object* v_a_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_443_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_441_, v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_444_, size_t v_i_445_, size_t v_stop_446_, lean_object* v_b_447_){
_start:
{
lean_object* v___y_449_; uint8_t v___x_453_; 
v___x_453_ = lean_usize_dec_eq(v_i_445_, v_stop_446_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_array_uget_borrowed(v_as_444_, v_i_445_);
if (lean_obj_tag(v___x_454_) == 0)
{
v___y_449_ = v_b_447_;
goto v___jp_448_;
}
else
{
lean_object* v_val_455_; lean_object* v___x_456_; 
v_val_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_val_455_);
v___x_456_ = lean_array_push(v_b_447_, v_val_455_);
v___y_449_ = v___x_456_;
goto v___jp_448_;
}
}
else
{
return v_b_447_;
}
v___jp_448_:
{
size_t v___x_450_; size_t v___x_451_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_445_, v___x_450_);
v_i_445_ = v___x_451_;
v_b_447_ = v___y_449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_stop_459_, lean_object* v_b_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_457_, v_i_boxed_461_, v_stop_boxed_462_, v_b_460_);
lean_dec_ref(v_as_457_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_466_, lean_object* v_start_467_, lean_object* v_stop_468_){
_start:
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_470_ = lean_nat_dec_lt(v_start_467_, v_stop_468_);
if (v___x_470_ == 0)
{
return v___x_469_;
}
else
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_array_get_size(v_as_466_);
v___x_472_ = lean_nat_dec_le(v_stop_468_, v___x_471_);
if (v___x_472_ == 0)
{
uint8_t v___x_473_; 
v___x_473_ = lean_nat_dec_lt(v_start_467_, v___x_471_);
if (v___x_473_ == 0)
{
return v___x_469_;
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_usize_of_nat(v_start_467_);
v___x_475_ = lean_usize_of_nat(v___x_471_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_466_, v___x_474_, v___x_475_, v___x_469_);
return v___x_476_;
}
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_usize_of_nat(v_start_467_);
v___x_478_ = lean_usize_of_nat(v_stop_468_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_466_, v___x_477_, v___x_478_, v___x_469_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_480_, lean_object* v_start_481_, lean_object* v_stop_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_480_, v_start_481_, v_stop_482_);
lean_dec(v_stop_482_);
lean_dec(v_start_481_);
lean_dec_ref(v_as_480_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t v_sz_484_, size_t v_i_485_, lean_object* v_bs_486_){
_start:
{
uint8_t v___x_487_; 
v___x_487_ = lean_usize_dec_lt(v_i_485_, v_sz_484_);
if (v___x_487_ == 0)
{
return v_bs_486_;
}
else
{
lean_object* v_v_488_; lean_object* v_diagnostics_489_; lean_object* v_msgLog_490_; lean_object* v___x_491_; lean_object* v_bs_x27_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v_v_488_ = lean_array_uget_borrowed(v_bs_486_, v_i_485_);
v_diagnostics_489_ = lean_ctor_get(v_v_488_, 1);
v_msgLog_490_ = lean_ctor_get(v_diagnostics_489_, 0);
lean_inc_ref(v_msgLog_490_);
v___x_491_ = lean_unsigned_to_nat(0u);
v_bs_x27_492_ = lean_array_uset(v_bs_486_, v_i_485_, v___x_491_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_485_, v___x_493_);
v___x_495_ = lean_array_uset(v_bs_x27_492_, v_i_485_, v_msgLog_490_);
v_i_485_ = v___x_494_;
v_bs_486_ = v___x_495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_sz_497_, lean_object* v_i_498_, lean_object* v_bs_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_497_);
lean_dec(v_sz_497_);
v_i_boxed_501_ = lean_unbox_usize(v_i_498_);
lean_dec(v_i_498_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_boxed_500_, v_i_boxed_501_, v_bs_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_503_, size_t v_i_504_, lean_object* v_bs_505_){
_start:
{
uint8_t v___x_506_; 
v___x_506_ = lean_usize_dec_lt(v_i_504_, v_sz_503_);
if (v___x_506_ == 0)
{
return v_bs_505_;
}
else
{
lean_object* v_v_507_; lean_object* v_elabSnap_508_; lean_object* v_infoTreeSnap_509_; lean_object* v___x_510_; lean_object* v_infoTree_x3f_511_; lean_object* v___x_512_; lean_object* v_bs_x27_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v_v_507_ = lean_array_uget_borrowed(v_bs_505_, v_i_504_);
v_elabSnap_508_ = lean_ctor_get(v_v_507_, 3);
v_infoTreeSnap_509_ = lean_ctor_get(v_elabSnap_508_, 3);
lean_inc_ref(v_infoTreeSnap_509_);
v___x_510_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_509_);
v_infoTree_x3f_511_ = lean_ctor_get(v___x_510_, 2);
lean_inc(v_infoTree_x3f_511_);
lean_dec(v___x_510_);
v___x_512_ = lean_unsigned_to_nat(0u);
v_bs_x27_513_ = lean_array_uset(v_bs_505_, v_i_504_, v___x_512_);
v___x_514_ = ((size_t)1ULL);
v___x_515_ = lean_usize_add(v_i_504_, v___x_514_);
v___x_516_ = lean_array_uset(v_bs_x27_513_, v_i_504_, v_infoTree_x3f_511_);
v_i_504_ = v___x_515_;
v_bs_505_ = v___x_516_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_bs_520_){
_start:
{
size_t v_sz_boxed_521_; size_t v_i_boxed_522_; lean_object* v_res_523_; 
v_sz_boxed_521_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_522_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_521_, v_i_boxed_522_, v_bs_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_524_, size_t v_i_525_, lean_object* v_bs_526_){
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
lean_object* v_v_528_; lean_object* v_stx_529_; lean_object* v___x_530_; lean_object* v_bs_x27_531_; size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v_v_528_ = lean_array_uget_borrowed(v_bs_526_, v_i_525_);
v_stx_529_ = lean_ctor_get(v_v_528_, 1);
lean_inc(v_stx_529_);
v___x_530_ = lean_unsigned_to_nat(0u);
v_bs_x27_531_ = lean_array_uset(v_bs_526_, v_i_525_, v___x_530_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_add(v_i_525_, v___x_532_);
v___x_534_ = lean_array_uset(v_bs_x27_531_, v_i_525_, v_stx_529_);
v_i_525_ = v___x_533_;
v_bs_526_ = v___x_534_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_536_, lean_object* v_i_537_, lean_object* v_bs_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_536_);
lean_dec(v_sz_536_);
v_i_boxed_540_ = lean_unbox_usize(v_i_537_);
lean_dec(v_i_537_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_539_, v_i_boxed_540_, v_bs_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object* v_as_542_, size_t v_i_543_, size_t v_stop_544_, lean_object* v_b_545_){
_start:
{
uint8_t v___x_546_; 
v___x_546_ = lean_usize_dec_eq(v_i_543_, v_stop_544_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; size_t v___x_549_; size_t v___x_550_; 
v___x_547_ = lean_array_uget_borrowed(v_as_542_, v_i_543_);
lean_inc(v___x_547_);
v___x_548_ = l_Lean_MessageLog_append(v_b_545_, v___x_547_);
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_543_, v___x_549_);
v_i_543_ = v___x_550_;
v_b_545_ = v___x_548_;
goto _start;
}
else
{
return v_b_545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object* v_as_552_, lean_object* v_i_553_, lean_object* v_stop_554_, lean_object* v_b_555_){
_start:
{
size_t v_i_boxed_556_; size_t v_stop_boxed_557_; lean_object* v_res_558_; 
v_i_boxed_556_ = lean_unbox_usize(v_i_553_);
lean_dec(v_i_553_);
v_stop_boxed_557_ = lean_unbox_usize(v_stop_554_);
lean_dec(v_stop_554_);
v_res_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v_as_552_, v_i_boxed_556_, v_stop_boxed_557_, v_b_555_);
lean_dec_ref(v_as_552_);
return v_res_558_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_unsigned_to_nat(32u);
v___x_560_ = lean_mk_empty_array_with_capacity(v___x_559_);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_562_ = ((size_t)5ULL);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_unsigned_to_nat(32u);
v___x_565_ = lean_mk_empty_array_with_capacity(v___x_564_);
v___x_566_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_567_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v___x_565_);
lean_ctor_set(v___x_567_, 2, v___x_563_);
lean_ctor_set(v___x_567_, 3, v___x_563_);
lean_ctor_set_usize(v___x_567_, 4, v___x_562_);
return v___x_567_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = l_Lean_NameSet_empty;
v___x_569_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
lean_ctor_set(v___x_570_, 2, v___x_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_571_, lean_object* v_initialSnap_572_, lean_object* v_t_573_, lean_object* v_commands_574_){
_start:
{
lean_object* v_snap_576_; lean_object* v_parserState_577_; lean_object* v_elabSnap_578_; lean_object* v_nextCmdSnap_x3f_579_; lean_object* v_commands_580_; 
v_snap_576_ = lean_task_get_own(v_t_573_);
v_parserState_577_ = lean_ctor_get(v_snap_576_, 2);
lean_inc_ref(v_parserState_577_);
v_elabSnap_578_ = lean_ctor_get(v_snap_576_, 3);
lean_inc_ref(v_elabSnap_578_);
v_nextCmdSnap_x3f_579_ = lean_ctor_get(v_snap_576_, 4);
lean_inc(v_nextCmdSnap_x3f_579_);
v_commands_580_ = lean_array_push(v_commands_574_, v_snap_576_);
if (lean_obj_tag(v_nextCmdSnap_x3f_579_) == 1)
{
lean_object* v_val_581_; lean_object* v_task_582_; 
lean_dec_ref(v_elabSnap_578_);
lean_dec_ref(v_parserState_577_);
v_val_581_ = lean_ctor_get(v_nextCmdSnap_x3f_579_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_nextCmdSnap_x3f_579_, 1);
v_task_582_ = lean_ctor_get(v_val_581_, 3);
lean_inc_ref(v_task_582_);
lean_dec(v_val_581_);
v_t_573_ = v_task_582_;
v_commands_574_ = v_commands_580_;
goto _start;
}
else
{
lean_object* v___x_584_; lean_object* v___y_586_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; size_t v_sz_632_; size_t v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
lean_dec(v_nextCmdSnap_x3f_579_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_572_);
v___x_630_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_initialSnap_572_);
v___x_631_ = l_Lean_Language_SnapshotTree_getAll(v___x_630_);
v_sz_632_ = lean_array_size(v___x_631_);
v___x_633_ = ((size_t)0ULL);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_632_, v___x_633_, v___x_631_);
v___x_635_ = lean_array_get_size(v___x_634_);
v___x_636_ = lean_nat_dec_lt(v___x_584_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec_ref(v___x_634_);
v___y_586_ = v___x_629_;
goto v___jp_585_;
}
else
{
uint8_t v___x_637_; 
v___x_637_ = lean_nat_dec_le(v___x_635_, v___x_635_);
if (v___x_637_ == 0)
{
if (v___x_636_ == 0)
{
lean_dec_ref(v___x_634_);
v___y_586_ = v___x_629_;
goto v___jp_585_;
}
else
{
size_t v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_usize_of_nat(v___x_635_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_634_, v___x_633_, v___x_638_, v___x_629_);
lean_dec_ref(v___x_634_);
v___y_586_ = v___x_639_;
goto v___jp_585_;
}
}
else
{
size_t v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_usize_of_nat(v___x_635_);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_634_, v___x_633_, v___x_640_, v___x_629_);
lean_dec_ref(v___x_634_);
v___y_586_ = v___x_641_;
goto v___jp_585_;
}
}
v___jp_585_:
{
size_t v_sz_587_; lean_object* v_resultSnap_588_; lean_object* v___x_589_; lean_object* v_cmdState_590_; lean_object* v_infoState_591_; lean_object* v_env_592_; lean_object* v_scopes_593_; lean_object* v_usedQuotCtxts_594_; lean_object* v_nextMacroScope_595_; lean_object* v_maxRecDepth_596_; lean_object* v_ngen_597_; lean_object* v_auxDeclNGen_598_; lean_object* v_traceState_599_; lean_object* v_snapshotTasks_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_627_; 
v_sz_587_ = lean_array_size(v_commands_580_);
v_resultSnap_588_ = lean_ctor_get(v_elabSnap_578_, 2);
lean_inc_ref(v_resultSnap_588_);
lean_dec_ref(v_elabSnap_578_);
v___x_589_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_588_);
v_cmdState_590_ = lean_ctor_get(v___x_589_, 1);
lean_inc_ref(v_cmdState_590_);
lean_dec(v___x_589_);
v_infoState_591_ = lean_ctor_get(v_cmdState_590_, 8);
v_env_592_ = lean_ctor_get(v_cmdState_590_, 0);
v_scopes_593_ = lean_ctor_get(v_cmdState_590_, 2);
v_usedQuotCtxts_594_ = lean_ctor_get(v_cmdState_590_, 3);
v_nextMacroScope_595_ = lean_ctor_get(v_cmdState_590_, 4);
v_maxRecDepth_596_ = lean_ctor_get(v_cmdState_590_, 5);
v_ngen_597_ = lean_ctor_get(v_cmdState_590_, 6);
v_auxDeclNGen_598_ = lean_ctor_get(v_cmdState_590_, 7);
v_traceState_599_ = lean_ctor_get(v_cmdState_590_, 9);
v_snapshotTasks_600_ = lean_ctor_get(v_cmdState_590_, 10);
v_isSharedCheck_627_ = !lean_is_exclusive(v_cmdState_590_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_cmdState_590_, 1);
lean_dec(v_unused_628_);
v___x_602_ = v_cmdState_590_;
v_isShared_603_ = v_isSharedCheck_627_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snapshotTasks_600_);
lean_inc(v_traceState_599_);
lean_inc(v_infoState_591_);
lean_inc(v_auxDeclNGen_598_);
lean_inc(v_ngen_597_);
lean_inc(v_maxRecDepth_596_);
lean_inc(v_nextMacroScope_595_);
lean_inc(v_usedQuotCtxts_594_);
lean_inc(v_scopes_593_);
lean_inc(v_env_592_);
lean_dec(v_cmdState_590_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_627_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
uint8_t v_enabled_604_; lean_object* v_assignment_605_; lean_object* v_lazyAssignment_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_625_; 
v_enabled_604_ = lean_ctor_get_uint8(v_infoState_591_, sizeof(void*)*3);
v_assignment_605_ = lean_ctor_get(v_infoState_591_, 0);
v_lazyAssignment_606_ = lean_ctor_get(v_infoState_591_, 1);
v_isSharedCheck_625_ = !lean_is_exclusive(v_infoState_591_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_infoState_591_, 2);
lean_dec(v_unused_626_);
v___x_608_ = v_infoState_591_;
v_isShared_609_ = v_isSharedCheck_625_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_lazyAssignment_606_);
lean_inc(v_assignment_605_);
lean_dec(v_infoState_591_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_625_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_pos_610_; size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_trees_615_; lean_object* v___x_617_; 
v_pos_610_ = lean_ctor_get(v_parserState_577_, 0);
lean_inc(v_pos_610_);
v___x_611_ = ((size_t)0ULL);
lean_inc_ref(v_commands_580_);
v___x_612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_587_, v___x_611_, v_commands_580_);
v___x_613_ = lean_array_get_size(v___x_612_);
v___x_614_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_612_, v___x_584_, v___x_613_);
lean_dec_ref(v___x_612_);
v_trees_615_ = l_Lean_Array_toPArray_x27___redArg(v___x_614_);
lean_dec_ref(v___x_614_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 2, v_trees_615_);
v___x_617_ = v___x_608_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_assignment_605_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_lazyAssignment_606_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_trees_615_);
lean_ctor_set_uint8(v_reuseFailAlloc_624_, sizeof(void*)*3, v_enabled_604_);
v___x_617_ = v_reuseFailAlloc_624_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 8, v___x_617_);
lean_ctor_set(v___x_602_, 1, v___y_586_);
v___x_619_ = v___x_602_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_env_592_);
lean_ctor_set(v_reuseFailAlloc_623_, 1, v___y_586_);
lean_ctor_set(v_reuseFailAlloc_623_, 2, v_scopes_593_);
lean_ctor_set(v_reuseFailAlloc_623_, 3, v_usedQuotCtxts_594_);
lean_ctor_set(v_reuseFailAlloc_623_, 4, v_nextMacroScope_595_);
lean_ctor_set(v_reuseFailAlloc_623_, 5, v_maxRecDepth_596_);
lean_ctor_set(v_reuseFailAlloc_623_, 6, v_ngen_597_);
lean_ctor_set(v_reuseFailAlloc_623_, 7, v_auxDeclNGen_598_);
lean_ctor_set(v_reuseFailAlloc_623_, 8, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_623_, 9, v_traceState_599_);
lean_ctor_set(v_reuseFailAlloc_623_, 10, v_snapshotTasks_600_);
v___x_619_ = v_reuseFailAlloc_623_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_587_, v___x_611_, v_commands_580_);
v___x_621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v_parserState_577_);
lean_ctor_set(v___x_621_, 2, v_pos_610_);
lean_ctor_set(v___x_621_, 3, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_inputCtx_571_);
lean_ctor_set(v___x_622_, 2, v_initialSnap_572_);
return v___x_622_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_642_, lean_object* v_initialSnap_643_, lean_object* v_t_644_, lean_object* v_commands_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_642_, v_initialSnap_643_, v_t_644_, v_commands_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_650_, lean_object* v_parserState_651_, lean_object* v_commandState_652_, lean_object* v_old_x3f_653_){
_start:
{
lean_object* v___y_656_; 
if (lean_obj_tag(v_old_x3f_653_) == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_box(0);
v___y_656_ = v___x_661_;
goto v___jp_655_;
}
else
{
lean_object* v_val_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_672_; 
v_val_662_ = lean_ctor_get(v_old_x3f_653_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_old_x3f_653_);
if (v_isSharedCheck_672_ == 0)
{
v___x_664_ = v_old_x3f_653_;
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_val_662_);
lean_dec(v_old_x3f_653_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_672_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v_inputCtx_666_; lean_object* v_initialSnap_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v_inputCtx_666_ = lean_ctor_get(v_val_662_, 1);
lean_inc_ref(v_inputCtx_666_);
v_initialSnap_667_ = lean_ctor_get(v_val_662_, 2);
lean_inc_ref(v_initialSnap_667_);
lean_dec(v_val_662_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v_inputCtx_666_);
lean_ctor_set(v___x_668_, 1, v_initialSnap_667_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_668_);
v___x_670_ = v___x_664_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
v___y_656_ = v___x_670_;
goto v___jp_655_;
}
}
}
v___jp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_657_ = l_Lean_Language_Lean_processCommands(v_inputCtx_650_, v_parserState_651_, v_commandState_652_, v___y_656_);
lean_inc_ref(v___x_657_);
v___x_658_ = lean_task_get_own(v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_660_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_650_, v___x_658_, v___x_657_, v___x_659_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_673_, lean_object* v_parserState_674_, lean_object* v_commandState_675_, lean_object* v_old_x3f_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_673_, v_parserState_674_, v_commandState_675_, v_old_x3f_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_679_, lean_object* v_parserState_680_, lean_object* v_commandState_681_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_toState_685_; lean_object* v___x_686_; 
v___x_683_ = lean_box(0);
v___x_684_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_679_, v_parserState_680_, v_commandState_681_, v___x_683_);
v_toState_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc_ref(v_toState_685_);
lean_dec_ref(v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_toState_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_687_, lean_object* v_parserState_688_, lean_object* v_commandState_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Elab_IO_processCommands(v_inputCtx_687_, v_parserState_688_, v_commandState_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_697_, lean_object* v_env_698_, lean_object* v_opts_699_, lean_object* v_fileName_700_){
_start:
{
lean_object* v___y_703_; 
if (lean_obj_tag(v_fileName_700_) == 0)
{
lean_object* v___x_723_; 
v___x_723_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_703_ = v___x_723_;
goto v___jp_702_;
}
else
{
lean_object* v_val_724_; 
v_val_724_ = lean_ctor_get(v_fileName_700_, 0);
lean_inc(v_val_724_);
lean_dec_ref_known(v_fileName_700_, 1);
v___y_703_ = v_val_724_;
goto v___jp_702_;
}
v___jp_702_:
{
uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v_inputCtx_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_722_; 
v___x_704_ = 1;
v___x_705_ = lean_string_utf8_byte_size(v_input_697_);
v_inputCtx_706_ = l_Lean_Parser_mkInputContext___redArg(v_input_697_, v___y_703_, v___x_704_, v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_708_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_709_ = l_Lean_Elab_Command_mkState(v_env_698_, v___x_708_, v_opts_699_);
v___x_710_ = l_Lean_Elab_IO_processCommands(v_inputCtx_706_, v___x_707_, v___x_709_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_722_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_722_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_722_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_commandState_715_; lean_object* v_env_716_; lean_object* v_messages_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v_commandState_715_ = lean_ctor_get(v_a_711_, 0);
lean_inc_ref(v_commandState_715_);
lean_dec(v_a_711_);
v_env_716_ = lean_ctor_get(v_commandState_715_, 0);
lean_inc_ref(v_env_716_);
v_messages_717_ = lean_ctor_get(v_commandState_715_, 1);
lean_inc_ref(v_messages_717_);
lean_dec_ref(v_commandState_715_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_env_716_);
lean_ctor_set(v___x_718_, 1, v_messages_717_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_718_);
v___x_720_ = v___x_713_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_725_, lean_object* v_env_726_, lean_object* v_opts_727_, lean_object* v_fileName_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Elab_process(v_input_725_, v_env_726_, v_opts_727_, v_fileName_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_731_, lean_object* v_cmdStx_x3f_732_, lean_object* v_acc_733_){
_start:
{
lean_object* v_element_734_; lean_object* v_diagnostics_735_; lean_object* v_children_736_; lean_object* v_msgLog_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_755_; 
v_element_734_ = lean_ctor_get(v_t_731_, 0);
v_diagnostics_735_ = lean_ctor_get(v_element_734_, 1);
lean_inc_ref(v_diagnostics_735_);
v_children_736_ = lean_ctor_get(v_t_731_, 1);
lean_inc_ref(v_children_736_);
lean_dec_ref(v_t_731_);
v_msgLog_737_ = lean_ctor_get(v_diagnostics_735_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_diagnostics_735_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_diagnostics_735_, 1);
lean_dec(v_unused_756_);
v___x_739_ = v_diagnostics_735_;
v_isShared_740_ = v_isSharedCheck_755_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_msgLog_737_);
lean_dec(v_diagnostics_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_755_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
lean_inc(v_cmdStx_x3f_732_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v_msgLog_737_);
lean_ctor_set(v___x_739_, 0, v_cmdStx_x3f_732_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_cmdStx_x3f_732_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_msgLog_737_);
v___x_742_ = v_reuseFailAlloc_754_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v_acc_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_acc_743_ = lean_array_push(v_acc_733_, v___x_742_);
v___x_744_ = lean_unsigned_to_nat(0u);
v___x_745_ = lean_array_get_size(v_children_736_);
v___x_746_ = lean_nat_dec_lt(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_dec_ref(v_children_736_);
lean_dec(v_cmdStx_x3f_732_);
return v_acc_743_;
}
else
{
uint8_t v___x_747_; 
v___x_747_ = lean_nat_dec_le(v___x_745_, v___x_745_);
if (v___x_747_ == 0)
{
if (v___x_746_ == 0)
{
lean_dec_ref(v_children_736_);
lean_dec(v_cmdStx_x3f_732_);
return v_acc_743_;
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_745_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_732_, v_children_736_, v___x_748_, v___x_749_, v_acc_743_);
lean_dec_ref(v_children_736_);
return v___x_750_;
}
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_745_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_732_, v_children_736_, v___x_751_, v___x_752_, v_acc_743_);
lean_dec_ref(v_children_736_);
return v___x_753_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_757_, lean_object* v_as_758_, size_t v_i_759_, size_t v_stop_760_, lean_object* v_b_761_){
_start:
{
lean_object* v___y_763_; uint8_t v___x_767_; 
v___x_767_ = lean_usize_dec_eq(v_i_759_, v_stop_760_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v_stx_x3f_769_; lean_object* v___x_770_; 
v___x_768_ = lean_array_uget_borrowed(v_as_758_, v_i_759_);
v_stx_x3f_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v___x_768_);
v___x_770_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_768_);
if (lean_obj_tag(v_stx_x3f_769_) == 0)
{
lean_object* v___x_771_; 
lean_inc(v_cmdStx_x3f_757_);
v___x_771_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_770_, v_cmdStx_x3f_757_, v_b_761_);
v___y_763_ = v___x_771_;
goto v___jp_762_;
}
else
{
lean_object* v___x_772_; 
lean_inc_ref(v_stx_x3f_769_);
v___x_772_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_770_, v_stx_x3f_769_, v_b_761_);
v___y_763_ = v___x_772_;
goto v___jp_762_;
}
}
else
{
lean_dec(v_cmdStx_x3f_757_);
return v_b_761_;
}
v___jp_762_:
{
size_t v___x_764_; size_t v___x_765_; 
v___x_764_ = ((size_t)1ULL);
v___x_765_ = lean_usize_add(v_i_759_, v___x_764_);
v_i_759_ = v___x_765_;
v_b_761_ = v___y_763_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_773_, lean_object* v_as_774_, lean_object* v_i_775_, lean_object* v_stop_776_, lean_object* v_b_777_){
_start:
{
size_t v_i_boxed_778_; size_t v_stop_boxed_779_; lean_object* v_res_780_; 
v_i_boxed_778_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_stop_boxed_779_ = lean_unbox_usize(v_stop_776_);
lean_dec(v_stop_776_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_773_, v_as_774_, v_i_boxed_778_, v_stop_boxed_779_, v_b_777_);
lean_dec_ref(v_as_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_lean_x3f_783_; lean_object* v_olean_x3f_784_; lean_object* v_oleanServer_x3f_785_; lean_object* v_ilean_x3f_786_; lean_object* v_irSig_x3f_787_; lean_object* v_ir_x3f_788_; lean_object* v_c_x3f_789_; lean_object* v_bc_x3f_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_798_; 
v_lean_x3f_783_ = lean_ctor_get(v_a_782_, 0);
v_olean_x3f_784_ = lean_ctor_get(v_a_782_, 1);
v_oleanServer_x3f_785_ = lean_ctor_get(v_a_782_, 2);
v_ilean_x3f_786_ = lean_ctor_get(v_a_782_, 4);
v_irSig_x3f_787_ = lean_ctor_get(v_a_782_, 5);
v_ir_x3f_788_ = lean_ctor_get(v_a_782_, 6);
v_c_x3f_789_ = lean_ctor_get(v_a_782_, 7);
v_bc_x3f_790_ = lean_ctor_get(v_a_782_, 8);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_782_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v_a_782_, 3);
lean_dec(v_unused_799_);
v___x_792_ = v_a_782_;
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_bc_x3f_790_);
lean_inc(v_c_x3f_789_);
lean_inc(v_ir_x3f_788_);
lean_inc(v_irSig_x3f_787_);
lean_inc(v_ilean_x3f_786_);
lean_inc(v_oleanServer_x3f_785_);
lean_inc(v_olean_x3f_784_);
lean_inc(v_lean_x3f_783_);
lean_dec(v_a_782_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_798_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v_filePath_781_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 3, v___x_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_lean_x3f_783_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_olean_x3f_784_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_oleanServer_x3f_785_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_ilean_x3f_786_);
lean_ctor_set(v_reuseFailAlloc_797_, 5, v_irSig_x3f_787_);
lean_ctor_set(v_reuseFailAlloc_797_, 6, v_ir_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_797_, 7, v_c_x3f_789_);
lean_ctor_set(v_reuseFailAlloc_797_, 8, v_bc_x3f_790_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_800_, lean_object* v_a_801_){
_start:
{
lean_object* v_lean_x3f_802_; lean_object* v_olean_x3f_803_; lean_object* v_oleanServer_x3f_804_; lean_object* v_oleanPrivate_x3f_805_; lean_object* v_ilean_x3f_806_; lean_object* v_ir_x3f_807_; lean_object* v_c_x3f_808_; lean_object* v_bc_x3f_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_817_; 
v_lean_x3f_802_ = lean_ctor_get(v_a_801_, 0);
v_olean_x3f_803_ = lean_ctor_get(v_a_801_, 1);
v_oleanServer_x3f_804_ = lean_ctor_get(v_a_801_, 2);
v_oleanPrivate_x3f_805_ = lean_ctor_get(v_a_801_, 3);
v_ilean_x3f_806_ = lean_ctor_get(v_a_801_, 4);
v_ir_x3f_807_ = lean_ctor_get(v_a_801_, 6);
v_c_x3f_808_ = lean_ctor_get(v_a_801_, 7);
v_bc_x3f_809_ = lean_ctor_get(v_a_801_, 8);
v_isSharedCheck_817_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v_a_801_, 5);
lean_dec(v_unused_818_);
v___x_811_ = v_a_801_;
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_bc_x3f_809_);
lean_inc(v_c_x3f_808_);
lean_inc(v_ir_x3f_807_);
lean_inc(v_ilean_x3f_806_);
lean_inc(v_oleanPrivate_x3f_805_);
lean_inc(v_oleanServer_x3f_804_);
lean_inc(v_olean_x3f_803_);
lean_inc(v_lean_x3f_802_);
lean_dec(v_a_801_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_817_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_813_, 0, v_filePath_800_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 5, v___x_813_);
v___x_815_ = v___x_811_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_lean_x3f_802_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_olean_x3f_803_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_oleanServer_x3f_804_);
lean_ctor_set(v_reuseFailAlloc_816_, 3, v_oleanPrivate_x3f_805_);
lean_ctor_set(v_reuseFailAlloc_816_, 4, v_ilean_x3f_806_);
lean_ctor_set(v_reuseFailAlloc_816_, 5, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 6, v_ir_x3f_807_);
lean_ctor_set(v_reuseFailAlloc_816_, 7, v_c_x3f_808_);
lean_ctor_set(v_reuseFailAlloc_816_, 8, v_bc_x3f_809_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_lean_x3f_821_; lean_object* v_olean_x3f_822_; lean_object* v_oleanPrivate_x3f_823_; lean_object* v_ilean_x3f_824_; lean_object* v_irSig_x3f_825_; lean_object* v_ir_x3f_826_; lean_object* v_c_x3f_827_; lean_object* v_bc_x3f_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
v_lean_x3f_821_ = lean_ctor_get(v_a_820_, 0);
v_olean_x3f_822_ = lean_ctor_get(v_a_820_, 1);
v_oleanPrivate_x3f_823_ = lean_ctor_get(v_a_820_, 3);
v_ilean_x3f_824_ = lean_ctor_get(v_a_820_, 4);
v_irSig_x3f_825_ = lean_ctor_get(v_a_820_, 5);
v_ir_x3f_826_ = lean_ctor_get(v_a_820_, 6);
v_c_x3f_827_ = lean_ctor_get(v_a_820_, 7);
v_bc_x3f_828_ = lean_ctor_get(v_a_820_, 8);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_820_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_a_820_, 2);
lean_dec(v_unused_837_);
v___x_830_ = v_a_820_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_bc_x3f_828_);
lean_inc(v_c_x3f_827_);
lean_inc(v_ir_x3f_826_);
lean_inc(v_irSig_x3f_825_);
lean_inc(v_ilean_x3f_824_);
lean_inc(v_oleanPrivate_x3f_823_);
lean_inc(v_olean_x3f_822_);
lean_inc(v_lean_x3f_821_);
lean_dec(v_a_820_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_832_, 0, v_filePath_819_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 2, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_lean_x3f_821_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_olean_x3f_822_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_oleanPrivate_x3f_823_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v_ilean_x3f_824_);
lean_ctor_set(v_reuseFailAlloc_835_, 5, v_irSig_x3f_825_);
lean_ctor_set(v_reuseFailAlloc_835_, 6, v_ir_x3f_826_);
lean_ctor_set(v_reuseFailAlloc_835_, 7, v_c_x3f_827_);
lean_ctor_set(v_reuseFailAlloc_835_, 8, v_bc_x3f_828_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
uint8_t v___x_840_; 
v___x_840_ = 0;
return v___x_840_;
}
else
{
lean_object* v_key_841_; lean_object* v_tail_842_; uint8_t v___x_843_; 
v_key_841_ = lean_ctor_get(v_x_839_, 0);
v_tail_842_ = lean_ctor_get(v_x_839_, 2);
v___x_843_ = lean_string_dec_eq(v_key_841_, v_a_838_);
if (v___x_843_ == 0)
{
v_x_839_ = v_tail_842_;
goto _start;
}
else
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_845_, lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_845_, v_x_846_);
lean_dec(v_x_846_);
lean_dec_ref(v_a_845_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_buckets_851_; lean_object* v___x_852_; uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v_fold_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v___x_859_; size_t v___x_860_; size_t v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v_buckets_851_ = lean_ctor_get(v_m_849_, 1);
v___x_852_ = lean_array_get_size(v_buckets_851_);
v___x_853_ = lean_string_hash(v_a_850_);
v___x_854_ = 32ULL;
v___x_855_ = lean_uint64_shift_right(v___x_853_, v___x_854_);
v_fold_856_ = lean_uint64_xor(v___x_853_, v___x_855_);
v___x_857_ = 16ULL;
v___x_858_ = lean_uint64_shift_right(v_fold_856_, v___x_857_);
v___x_859_ = lean_uint64_xor(v_fold_856_, v___x_858_);
v___x_860_ = lean_uint64_to_usize(v___x_859_);
v___x_861_ = lean_usize_of_nat(v___x_852_);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_sub(v___x_861_, v___x_862_);
v___x_864_ = lean_usize_land(v___x_860_, v___x_863_);
v___x_865_ = lean_array_uget_borrowed(v_buckets_851_, v___x_864_);
v___x_866_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_850_, v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_867_, lean_object* v_a_868_){
_start:
{
uint8_t v_res_869_; lean_object* v_r_870_; 
v_res_869_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_867_, v_a_868_);
lean_dec_ref(v_a_868_);
lean_dec_ref(v_m_867_);
v_r_870_ = lean_box(v_res_869_);
return v_r_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_871_, lean_object* v_fallback_872_, lean_object* v_x_873_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_inc(v_fallback_872_);
return v_fallback_872_;
}
else
{
lean_object* v_key_874_; lean_object* v_value_875_; lean_object* v_tail_876_; uint8_t v___x_877_; 
v_key_874_ = lean_ctor_get(v_x_873_, 0);
v_value_875_ = lean_ctor_get(v_x_873_, 1);
v_tail_876_ = lean_ctor_get(v_x_873_, 2);
v___x_877_ = lean_string_dec_eq(v_key_874_, v_a_871_);
if (v___x_877_ == 0)
{
v_x_873_ = v_tail_876_;
goto _start;
}
else
{
lean_inc(v_value_875_);
return v_value_875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_879_, lean_object* v_fallback_880_, lean_object* v_x_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_879_, v_fallback_880_, v_x_881_);
lean_dec(v_x_881_);
lean_dec(v_fallback_880_);
lean_dec_ref(v_a_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_883_, lean_object* v_a_884_, lean_object* v_fallback_885_){
_start:
{
lean_object* v_buckets_886_; lean_object* v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; uint64_t v___x_890_; uint64_t v_fold_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; size_t v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_buckets_886_ = lean_ctor_get(v_m_883_, 1);
v___x_887_ = lean_array_get_size(v_buckets_886_);
v___x_888_ = lean_string_hash(v_a_884_);
v___x_889_ = 32ULL;
v___x_890_ = lean_uint64_shift_right(v___x_888_, v___x_889_);
v_fold_891_ = lean_uint64_xor(v___x_888_, v___x_890_);
v___x_892_ = 16ULL;
v___x_893_ = lean_uint64_shift_right(v_fold_891_, v___x_892_);
v___x_894_ = lean_uint64_xor(v_fold_891_, v___x_893_);
v___x_895_ = lean_uint64_to_usize(v___x_894_);
v___x_896_ = lean_usize_of_nat(v___x_887_);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_sub(v___x_896_, v___x_897_);
v___x_899_ = lean_usize_land(v___x_895_, v___x_898_);
v___x_900_ = lean_array_uget_borrowed(v_buckets_886_, v___x_899_);
v___x_901_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_884_, v_fallback_885_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_902_, lean_object* v_a_903_, lean_object* v_fallback_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_902_, v_a_903_, v_fallback_904_);
lean_dec(v_fallback_904_);
lean_dec_ref(v_a_903_);
lean_dec_ref(v_m_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_lean_x3f_908_; lean_object* v_olean_x3f_909_; lean_object* v_oleanServer_x3f_910_; lean_object* v_oleanPrivate_x3f_911_; lean_object* v_ilean_x3f_912_; lean_object* v_irSig_x3f_913_; lean_object* v_c_x3f_914_; lean_object* v_bc_x3f_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_lean_x3f_908_ = lean_ctor_get(v_a_907_, 0);
v_olean_x3f_909_ = lean_ctor_get(v_a_907_, 1);
v_oleanServer_x3f_910_ = lean_ctor_get(v_a_907_, 2);
v_oleanPrivate_x3f_911_ = lean_ctor_get(v_a_907_, 3);
v_ilean_x3f_912_ = lean_ctor_get(v_a_907_, 4);
v_irSig_x3f_913_ = lean_ctor_get(v_a_907_, 5);
v_c_x3f_914_ = lean_ctor_get(v_a_907_, 7);
v_bc_x3f_915_ = lean_ctor_get(v_a_907_, 8);
v_isSharedCheck_923_ = !lean_is_exclusive(v_a_907_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_a_907_, 6);
lean_dec(v_unused_924_);
v___x_917_ = v_a_907_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_bc_x3f_915_);
lean_inc(v_c_x3f_914_);
lean_inc(v_irSig_x3f_913_);
lean_inc(v_ilean_x3f_912_);
lean_inc(v_oleanPrivate_x3f_911_);
lean_inc(v_oleanServer_x3f_910_);
lean_inc(v_olean_x3f_909_);
lean_inc(v_lean_x3f_908_);
lean_dec(v_a_907_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_919_, 0, v_filePath_906_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 6, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_lean_x3f_908_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_olean_x3f_909_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_oleanServer_x3f_910_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_oleanPrivate_x3f_911_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_ilean_x3f_912_);
lean_ctor_set(v_reuseFailAlloc_922_, 5, v_irSig_x3f_913_);
lean_ctor_set(v_reuseFailAlloc_922_, 6, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_922_, 7, v_c_x3f_914_);
lean_ctor_set(v_reuseFailAlloc_922_, 8, v_bc_x3f_915_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_lean_x3f_927_; lean_object* v_oleanServer_x3f_928_; lean_object* v_oleanPrivate_x3f_929_; lean_object* v_ilean_x3f_930_; lean_object* v_irSig_x3f_931_; lean_object* v_ir_x3f_932_; lean_object* v_c_x3f_933_; lean_object* v_bc_x3f_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_942_; 
v_lean_x3f_927_ = lean_ctor_get(v_a_926_, 0);
v_oleanServer_x3f_928_ = lean_ctor_get(v_a_926_, 2);
v_oleanPrivate_x3f_929_ = lean_ctor_get(v_a_926_, 3);
v_ilean_x3f_930_ = lean_ctor_get(v_a_926_, 4);
v_irSig_x3f_931_ = lean_ctor_get(v_a_926_, 5);
v_ir_x3f_932_ = lean_ctor_get(v_a_926_, 6);
v_c_x3f_933_ = lean_ctor_get(v_a_926_, 7);
v_bc_x3f_934_ = lean_ctor_get(v_a_926_, 8);
v_isSharedCheck_942_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v_a_926_, 1);
lean_dec(v_unused_943_);
v___x_936_ = v_a_926_;
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_bc_x3f_934_);
lean_inc(v_c_x3f_933_);
lean_inc(v_ir_x3f_932_);
lean_inc(v_irSig_x3f_931_);
lean_inc(v_ilean_x3f_930_);
lean_inc(v_oleanPrivate_x3f_929_);
lean_inc(v_oleanServer_x3f_928_);
lean_inc(v_lean_x3f_927_);
lean_dec(v_a_926_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_942_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_938_, 0, v_filePath_925_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 1, v___x_938_);
v___x_940_ = v___x_936_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_lean_x3f_927_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_938_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_oleanServer_x3f_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_oleanPrivate_x3f_929_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_ilean_x3f_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 5, v_irSig_x3f_931_);
lean_ctor_set(v_reuseFailAlloc_941_, 6, v_ir_x3f_932_);
lean_ctor_set(v_reuseFailAlloc_941_, 7, v_c_x3f_933_);
lean_ctor_set(v_reuseFailAlloc_941_, 8, v_bc_x3f_934_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_944_, lean_object* v_b_945_, lean_object* v_x_946_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_dec(v_b_945_);
lean_dec_ref(v_a_944_);
return v_x_946_;
}
else
{
lean_object* v_key_947_; lean_object* v_value_948_; lean_object* v_tail_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_961_; 
v_key_947_ = lean_ctor_get(v_x_946_, 0);
v_value_948_ = lean_ctor_get(v_x_946_, 1);
v_tail_949_ = lean_ctor_get(v_x_946_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v_x_946_);
if (v_isSharedCheck_961_ == 0)
{
v___x_951_ = v_x_946_;
v_isShared_952_ = v_isSharedCheck_961_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_tail_949_);
lean_inc(v_value_948_);
lean_inc(v_key_947_);
lean_dec(v_x_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_961_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
uint8_t v___x_953_; 
v___x_953_ = lean_string_dec_eq(v_key_947_, v_a_944_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_944_, v_b_945_, v_tail_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 2, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_key_947_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_value_948_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
else
{
lean_object* v___x_959_; 
lean_dec(v_value_948_);
lean_dec(v_key_947_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 1, v_b_945_);
lean_ctor_set(v___x_951_, 0, v_a_944_);
v___x_959_ = v___x_951_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_944_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_b_945_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_tail_949_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
if (lean_obj_tag(v_x_963_) == 0)
{
return v_x_962_;
}
else
{
lean_object* v_key_964_; lean_object* v_value_965_; lean_object* v_tail_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_989_; 
v_key_964_ = lean_ctor_get(v_x_963_, 0);
v_value_965_ = lean_ctor_get(v_x_963_, 1);
v_tail_966_ = lean_ctor_get(v_x_963_, 2);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_963_);
if (v_isSharedCheck_989_ == 0)
{
v___x_968_ = v_x_963_;
v_isShared_969_ = v_isSharedCheck_989_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_tail_966_);
lean_inc(v_value_965_);
lean_inc(v_key_964_);
lean_dec(v_x_963_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_989_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; uint64_t v___x_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v_fold_974_; uint64_t v___x_975_; uint64_t v___x_976_; uint64_t v___x_977_; size_t v___x_978_; size_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_970_ = lean_array_get_size(v_x_962_);
v___x_971_ = lean_string_hash(v_key_964_);
v___x_972_ = 32ULL;
v___x_973_ = lean_uint64_shift_right(v___x_971_, v___x_972_);
v_fold_974_ = lean_uint64_xor(v___x_971_, v___x_973_);
v___x_975_ = 16ULL;
v___x_976_ = lean_uint64_shift_right(v_fold_974_, v___x_975_);
v___x_977_ = lean_uint64_xor(v_fold_974_, v___x_976_);
v___x_978_ = lean_uint64_to_usize(v___x_977_);
v___x_979_ = lean_usize_of_nat(v___x_970_);
v___x_980_ = ((size_t)1ULL);
v___x_981_ = lean_usize_sub(v___x_979_, v___x_980_);
v___x_982_ = lean_usize_land(v___x_978_, v___x_981_);
v___x_983_ = lean_array_uget_borrowed(v_x_962_, v___x_982_);
lean_inc(v___x_983_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 2, v___x_983_);
v___x_985_ = v___x_968_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_key_964_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_value_965_);
lean_ctor_set(v_reuseFailAlloc_988_, 2, v___x_983_);
v___x_985_ = v_reuseFailAlloc_988_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; 
v___x_986_ = lean_array_uset(v_x_962_, v___x_982_, v___x_985_);
v_x_962_ = v___x_986_;
v_x_963_ = v_tail_966_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_990_, lean_object* v_source_991_, lean_object* v_target_992_){
_start:
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = lean_array_get_size(v_source_991_);
v___x_994_ = lean_nat_dec_lt(v_i_990_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v_source_991_);
lean_dec(v_i_990_);
return v_target_992_;
}
else
{
lean_object* v_es_995_; lean_object* v___x_996_; lean_object* v_source_997_; lean_object* v_target_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v_es_995_ = lean_array_fget(v_source_991_, v_i_990_);
v___x_996_ = lean_box(0);
v_source_997_ = lean_array_fset(v_source_991_, v_i_990_, v___x_996_);
v_target_998_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_992_, v_es_995_);
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_add(v_i_990_, v___x_999_);
lean_dec(v_i_990_);
v_i_990_ = v___x_1000_;
v_source_991_ = v_source_997_;
v_target_992_ = v_target_998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_1002_){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_nbuckets_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1003_ = lean_array_get_size(v_data_1002_);
v___x_1004_ = lean_unsigned_to_nat(2u);
v_nbuckets_1005_ = lean_nat_mul(v___x_1003_, v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_mk_array(v_nbuckets_1005_, v___x_1007_);
v___x_1009_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1006_, v_data_1002_, v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1010_, lean_object* v_a_1011_, lean_object* v_b_1012_){
_start:
{
lean_object* v_size_1013_; lean_object* v_buckets_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1057_; 
v_size_1013_ = lean_ctor_get(v_m_1010_, 0);
v_buckets_1014_ = lean_ctor_get(v_m_1010_, 1);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_m_1010_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1016_ = v_m_1010_;
v_isShared_1017_ = v_isSharedCheck_1057_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_buckets_1014_);
lean_inc(v_size_1013_);
lean_dec(v_m_1010_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1057_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; uint64_t v___x_1019_; uint64_t v___x_1020_; uint64_t v___x_1021_; uint64_t v_fold_1022_; uint64_t v___x_1023_; uint64_t v___x_1024_; uint64_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; lean_object* v_bkt_1031_; uint8_t v___x_1032_; 
v___x_1018_ = lean_array_get_size(v_buckets_1014_);
v___x_1019_ = lean_string_hash(v_a_1011_);
v___x_1020_ = 32ULL;
v___x_1021_ = lean_uint64_shift_right(v___x_1019_, v___x_1020_);
v_fold_1022_ = lean_uint64_xor(v___x_1019_, v___x_1021_);
v___x_1023_ = 16ULL;
v___x_1024_ = lean_uint64_shift_right(v_fold_1022_, v___x_1023_);
v___x_1025_ = lean_uint64_xor(v_fold_1022_, v___x_1024_);
v___x_1026_ = lean_uint64_to_usize(v___x_1025_);
v___x_1027_ = lean_usize_of_nat(v___x_1018_);
v___x_1028_ = ((size_t)1ULL);
v___x_1029_ = lean_usize_sub(v___x_1027_, v___x_1028_);
v___x_1030_ = lean_usize_land(v___x_1026_, v___x_1029_);
v_bkt_1031_ = lean_array_uget_borrowed(v_buckets_1014_, v___x_1030_);
v___x_1032_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1011_, v_bkt_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v_size_x27_1034_; lean_object* v___x_1035_; lean_object* v_buckets_x27_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v___x_1033_ = lean_unsigned_to_nat(1u);
v_size_x27_1034_ = lean_nat_add(v_size_1013_, v___x_1033_);
lean_dec(v_size_1013_);
lean_inc(v_bkt_1031_);
v___x_1035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1035_, 0, v_a_1011_);
lean_ctor_set(v___x_1035_, 1, v_b_1012_);
lean_ctor_set(v___x_1035_, 2, v_bkt_1031_);
v_buckets_x27_1036_ = lean_array_uset(v_buckets_1014_, v___x_1030_, v___x_1035_);
v___x_1037_ = lean_unsigned_to_nat(4u);
v___x_1038_ = lean_nat_mul(v_size_x27_1034_, v___x_1037_);
v___x_1039_ = lean_unsigned_to_nat(3u);
v___x_1040_ = lean_nat_div(v___x_1038_, v___x_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_array_get_size(v_buckets_x27_1036_);
v___x_1042_ = lean_nat_dec_le(v___x_1040_, v___x_1041_);
lean_dec(v___x_1040_);
if (v___x_1042_ == 0)
{
lean_object* v_val_1043_; lean_object* v___x_1045_; 
v_val_1043_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1036_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v_val_1043_);
lean_ctor_set(v___x_1016_, 0, v_size_x27_1034_);
v___x_1045_ = v___x_1016_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_size_x27_1034_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_val_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
else
{
lean_object* v___x_1048_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v_buckets_x27_1036_);
lean_ctor_set(v___x_1016_, 0, v_size_x27_1034_);
v___x_1048_ = v___x_1016_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_size_x27_1034_);
lean_ctor_set(v_reuseFailAlloc_1049_, 1, v_buckets_x27_1036_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v___x_1050_; lean_object* v_buckets_x27_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_inc(v_bkt_1031_);
v___x_1050_ = lean_box(0);
v_buckets_x27_1051_ = lean_array_uset(v_buckets_1014_, v___x_1030_, v___x_1050_);
v___x_1052_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1011_, v_b_1012_, v_bkt_1031_);
v___x_1053_ = lean_array_uset(v_buckets_x27_1051_, v___x_1030_, v___x_1052_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v___x_1053_);
v___x_1055_ = v___x_1016_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_size_1013_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1066_, size_t v_sz_1067_, size_t v_i_1068_, lean_object* v_b_1069_){
_start:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_usize_dec_lt(v_i_1068_, v_sz_1067_);
if (v___x_1070_ == 0)
{
return v_b_1069_;
}
else
{
lean_object* v_fst_1071_; lean_object* v_snd_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1122_; 
v_fst_1071_ = lean_ctor_get(v_b_1069_, 0);
v_snd_1072_ = lean_ctor_get(v_b_1069_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_b_1069_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1074_ = v_b_1069_;
v_isShared_1075_ = v_isSharedCheck_1122_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_snd_1072_);
lean_inc(v_fst_1071_);
lean_dec(v_b_1069_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1122_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v_order_1079_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v_a_1095_; lean_object* v_filePath_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; 
v_a_1095_ = lean_array_uget_borrowed(v_as_1066_, v_i_1068_);
v_filePath_1096_ = lean_ctor_get(v_a_1095_, 0);
lean_inc_ref_n(v_filePath_1096_, 2);
v___f_1097_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1097_, 0, v_filePath_1096_);
v___x_1098_ = l_System_FilePath_extension(v_filePath_1096_);
if (lean_obj_tag(v___x_1098_) == 1)
{
lean_object* v_val_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_val_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_val_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1101_ = lean_string_dec_eq(v_val_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1103_ = lean_string_dec_eq(v_val_1099_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1105_ = lean_string_dec_eq(v_val_1099_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1107_ = lean_string_dec_eq(v_val_1099_, v___x_1106_);
lean_dec(v_val_1099_);
if (v___x_1107_ == 0)
{
lean_inc_ref(v_filePath_1096_);
v_fst_1091_ = v_filePath_1096_;
v_snd_1092_ = v___f_1097_;
goto v___jp_1090_;
}
else
{
lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec_ref(v___f_1097_);
lean_inc_ref_n(v_filePath_1096_, 2);
v___f_1108_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1108_, 0, v_filePath_1096_);
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1110_ = l_System_FilePath_withExtension(v_filePath_1096_, v___x_1109_);
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1112_ = l_System_FilePath_withExtension(v___x_1110_, v___x_1111_);
v_fst_1091_ = v___x_1112_;
v_snd_1092_ = v___f_1108_;
goto v___jp_1090_;
}
}
else
{
lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_dec(v_val_1099_);
lean_dec_ref(v___f_1097_);
lean_inc_ref_n(v_filePath_1096_, 2);
v___f_1113_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1113_, 0, v_filePath_1096_);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1115_ = l_System_FilePath_withExtension(v_filePath_1096_, v___x_1114_);
v_fst_1091_ = v___x_1115_;
v_snd_1092_ = v___f_1113_;
goto v___jp_1090_;
}
}
else
{
lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec(v_val_1099_);
lean_dec_ref(v___f_1097_);
lean_inc_ref_n(v_filePath_1096_, 2);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1116_, 0, v_filePath_1096_);
v___x_1117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1118_ = l_System_FilePath_withExtension(v_filePath_1096_, v___x_1117_);
v_fst_1091_ = v___x_1118_;
v_snd_1092_ = v___f_1116_;
goto v___jp_1090_;
}
}
else
{
lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec(v_val_1099_);
lean_dec_ref(v___f_1097_);
lean_inc_ref_n(v_filePath_1096_, 2);
v___f_1119_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1119_, 0, v_filePath_1096_);
v___x_1120_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1121_ = l_System_FilePath_withExtension(v_filePath_1096_, v___x_1120_);
v_fst_1091_ = v___x_1121_;
v_snd_1092_ = v___f_1119_;
goto v___jp_1090_;
}
}
else
{
lean_dec(v___x_1098_);
lean_inc_ref(v_filePath_1096_);
v_fst_1091_ = v_filePath_1096_;
v_snd_1092_ = v___f_1097_;
goto v___jp_1090_;
}
v___jp_1076_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1072_, v___y_1077_, v___x_1080_);
v___x_1082_ = lean_apply_1(v___y_1078_, v___x_1081_);
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1072_, v___y_1077_, v___x_1082_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v___x_1083_);
lean_ctor_set(v___x_1074_, 0, v_order_1079_);
v___x_1085_ = v___x_1074_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_order_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
size_t v___x_1086_; size_t v___x_1087_; 
v___x_1086_ = ((size_t)1ULL);
v___x_1087_ = lean_usize_add(v_i_1068_, v___x_1086_);
v_i_1068_ = v___x_1087_;
v_b_1069_ = v___x_1085_;
goto _start;
}
}
v___jp_1090_:
{
uint8_t v___x_1093_; 
v___x_1093_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1072_, v_fst_1091_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_inc_ref(v_fst_1091_);
v___x_1094_ = lean_array_push(v_fst_1071_, v_fst_1091_);
v___y_1077_ = v_fst_1091_;
v___y_1078_ = v_snd_1092_;
v_order_1079_ = v___x_1094_;
goto v___jp_1076_;
}
else
{
v___y_1077_ = v_fst_1091_;
v___y_1078_ = v_snd_1092_;
v_order_1079_ = v_fst_1071_;
goto v___jp_1076_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1123_, lean_object* v_sz_1124_, lean_object* v_i_1125_, lean_object* v_b_1126_){
_start:
{
size_t v_sz_boxed_1127_; size_t v_i_boxed_1128_; lean_object* v_res_1129_; 
v_sz_boxed_1127_ = lean_unbox_usize(v_sz_1124_);
lean_dec(v_sz_1124_);
v_i_boxed_1128_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1123_, v_sz_boxed_1127_, v_i_boxed_1128_, v_b_1126_);
lean_dec_ref(v_as_1123_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1130_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1132_ = lean_panic_fn_borrowed(v___x_1131_, v_msg_1130_);
return v___x_1132_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1136_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1137_ = lean_unsigned_to_nat(11u);
v___x_1138_ = lean_unsigned_to_nat(163u);
v___x_1139_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1140_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1141_ = l_mkPanicMessageWithDecl(v___x_1140_, v___x_1139_, v___x_1138_, v___x_1137_, v___x_1136_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1142_, lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1144_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1145_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1144_);
return v___x_1145_;
}
else
{
lean_object* v_key_1146_; lean_object* v_value_1147_; lean_object* v_tail_1148_; uint8_t v___x_1149_; 
v_key_1146_ = lean_ctor_get(v_x_1143_, 0);
v_value_1147_ = lean_ctor_get(v_x_1143_, 1);
v_tail_1148_ = lean_ctor_get(v_x_1143_, 2);
v___x_1149_ = lean_string_dec_eq(v_key_1146_, v_a_1142_);
if (v___x_1149_ == 0)
{
v_x_1143_ = v_tail_1148_;
goto _start;
}
else
{
lean_inc(v_value_1147_);
return v_value_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1151_, v_x_1152_);
lean_dec(v_x_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_buckets_1156_; lean_object* v___x_1157_; uint64_t v___x_1158_; uint64_t v___x_1159_; uint64_t v___x_1160_; uint64_t v_fold_1161_; uint64_t v___x_1162_; uint64_t v___x_1163_; uint64_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v_buckets_1156_ = lean_ctor_get(v_m_1154_, 1);
v___x_1157_ = lean_array_get_size(v_buckets_1156_);
v___x_1158_ = lean_string_hash(v_a_1155_);
v___x_1159_ = 32ULL;
v___x_1160_ = lean_uint64_shift_right(v___x_1158_, v___x_1159_);
v_fold_1161_ = lean_uint64_xor(v___x_1158_, v___x_1160_);
v___x_1162_ = 16ULL;
v___x_1163_ = lean_uint64_shift_right(v_fold_1161_, v___x_1162_);
v___x_1164_ = lean_uint64_xor(v_fold_1161_, v___x_1163_);
v___x_1165_ = lean_uint64_to_usize(v___x_1164_);
v___x_1166_ = lean_usize_of_nat(v___x_1157_);
v___x_1167_ = ((size_t)1ULL);
v___x_1168_ = lean_usize_sub(v___x_1166_, v___x_1167_);
v___x_1169_ = lean_usize_land(v___x_1165_, v___x_1168_);
v___x_1170_ = lean_array_uget_borrowed(v_buckets_1156_, v___x_1169_);
v___x_1171_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1155_, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1172_, v_a_1173_);
lean_dec_ref(v_a_1173_);
lean_dec_ref(v_m_1172_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1175_, size_t v_sz_1176_, size_t v_i_1177_, lean_object* v_bs_1178_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_usize_dec_lt(v_i_1177_, v_sz_1176_);
if (v___x_1179_ == 0)
{
return v_bs_1178_;
}
else
{
lean_object* v_v_1180_; lean_object* v___x_1181_; lean_object* v_bs_x27_1182_; lean_object* v___x_1183_; size_t v___x_1184_; size_t v___x_1185_; lean_object* v___x_1186_; 
v_v_1180_ = lean_array_uget(v_bs_1178_, v_i_1177_);
v___x_1181_ = lean_unsigned_to_nat(0u);
v_bs_x27_1182_ = lean_array_uset(v_bs_1178_, v_i_1177_, v___x_1181_);
v___x_1183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1175_, v_v_1180_);
lean_dec(v_v_1180_);
v___x_1184_ = ((size_t)1ULL);
v___x_1185_ = lean_usize_add(v_i_1177_, v___x_1184_);
v___x_1186_ = lean_array_uset(v_bs_x27_1182_, v_i_1177_, v___x_1183_);
v_i_1177_ = v___x_1185_;
v_bs_1178_ = v___x_1186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1188_, lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_bs_1191_){
_start:
{
size_t v_sz_boxed_1192_; size_t v_i_boxed_1193_; lean_object* v_res_1194_; 
v_sz_boxed_1192_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1193_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1188_, v_sz_boxed_1192_, v_i_boxed_1193_, v_bs_1191_);
lean_dec_ref(v___x_1188_);
return v_res_1194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_box(0);
v___x_1198_ = lean_unsigned_to_nat(16u);
v___x_1199_ = lean_mk_array(v___x_1198_, v___x_1197_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_byBase_1202_; 
v___x_1200_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1201_ = lean_unsigned_to_nat(0u);
v_byBase_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1202_, 0, v___x_1201_);
lean_ctor_set(v_byBase_1202_, 1, v___x_1200_);
return v_byBase_1202_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1203_; lean_object* v_order_1204_; lean_object* v___x_1205_; 
v_byBase_1203_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1204_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v_order_1204_);
lean_ctor_set(v___x_1205_, 1, v_byBase_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1206_){
_start:
{
lean_object* v___x_1207_; size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; lean_object* v_fst_1211_; lean_object* v_snd_1212_; size_t v_sz_1213_; lean_object* v___x_1214_; 
v___x_1207_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1208_ = lean_array_size(v_regions_1206_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1206_, v_sz_1208_, v___x_1209_, v___x_1207_);
v_fst_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_fst_1211_);
v_snd_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc(v_snd_1212_);
lean_dec_ref(v___x_1210_);
v_sz_1213_ = lean_array_size(v_fst_1211_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1212_, v_sz_1213_, v___x_1209_, v_fst_1211_);
lean_dec(v_snd_1212_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1215_);
lean_dec_ref(v_regions_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1217_, lean_object* v_m_1218_, lean_object* v_a_1219_, lean_object* v_fallback_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1218_, v_a_1219_, v_fallback_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_, lean_object* v_fallback_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1222_, v_m_1223_, v_a_1224_, v_fallback_1225_);
lean_dec(v_fallback_1225_);
lean_dec_ref(v_a_1224_);
lean_dec_ref(v_m_1223_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1227_, lean_object* v_m_1228_, lean_object* v_a_1229_, lean_object* v_b_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1228_, v_a_1229_, v_b_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1232_, lean_object* v_m_1233_, lean_object* v_a_1234_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1233_, v_a_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1236_, lean_object* v_m_1237_, lean_object* v_a_1238_){
_start:
{
uint8_t v_res_1239_; lean_object* v_r_1240_; 
v_res_1239_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1236_, v_m_1237_, v_a_1238_);
lean_dec_ref(v_a_1238_);
lean_dec_ref(v_m_1237_);
v_r_1240_ = lean_box(v_res_1239_);
return v_r_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1241_, lean_object* v_a_1242_, lean_object* v_fallback_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1242_, v_fallback_1243_, v_x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_a_1247_, lean_object* v_fallback_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1246_, v_a_1247_, v_fallback_1248_, v_x_1249_);
lean_dec(v_x_1249_);
lean_dec(v_fallback_1248_);
lean_dec_ref(v_a_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1251_, lean_object* v_a_1252_, lean_object* v_x_1253_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1252_, v_x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1255_, lean_object* v_a_1256_, lean_object* v_x_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1255_, v_a_1256_, v_x_1257_);
lean_dec(v_x_1257_);
lean_dec_ref(v_a_1256_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1260_, lean_object* v_data_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1264_, v_b_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1268_, lean_object* v_i_1269_, lean_object* v_source_1270_, lean_object* v_target_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1269_, v_source_1270_, v_target_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1274_, v_x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1277_, size_t v_sz_1278_, size_t v_i_1279_, lean_object* v_b_1280_){
_start:
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_usize_dec_lt(v_i_1279_, v_sz_1278_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_b_1280_);
return v___x_1283_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1285_; 
v_a_1284_ = lean_array_uget_borrowed(v_as_1277_, v_i_1279_);
v___x_1285_ = lean_compacted_region_read(v_a_1284_, v_b_1280_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v_snd_1287_; lean_object* v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v_snd_1287_ = lean_ctor_get(v_a_1286_, 1);
lean_inc(v_snd_1287_);
lean_dec(v_a_1286_);
v___x_1288_ = lean_array_push(v_b_1280_, v_snd_1287_);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_add(v_i_1279_, v___x_1289_);
v_i_1279_ = v___x_1290_;
v_b_1280_ = v___x_1288_;
goto _start;
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_b_1280_);
v_a_1292_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1285_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1285_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1300_, lean_object* v_sz_1301_, lean_object* v_i_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_){
_start:
{
size_t v_sz_boxed_1305_; size_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1301_);
lean_dec(v_sz_1301_);
v_i_boxed_1306_ = lean_unbox_usize(v_i_1302_);
lean_dec(v_i_1302_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1300_, v_sz_boxed_1305_, v_i_boxed_1306_, v_b_1303_);
lean_dec_ref(v_as_1300_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1310_){
_start:
{
lean_object* v_oleanRegions_1312_; lean_object* v___x_1313_; size_t v_sz_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v_oleanRegions_1312_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1310_);
v___x_1313_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1310_);
v_sz_1314_ = lean_array_size(v___x_1313_);
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1313_, v_sz_1314_, v___x_1315_, v_oleanRegions_1312_);
lean_dec_ref(v___x_1313_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; size_t v_sz_1319_; lean_object* v___x_1320_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = l_Lean_ModuleArtifacts_irParts(v_arts_1310_);
v_sz_1319_ = lean_array_size(v___x_1318_);
v___x_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1318_, v_sz_1319_, v___x_1315_, v_oleanRegions_1312_);
lean_dec_ref(v___x_1318_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1329_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1329_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = l_Array_append___redArg(v_a_1317_, v_a_1321_);
lean_dec(v_a_1321_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1325_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_dec(v_a_1317_);
return v___x_1320_;
}
}
else
{
lean_dec_ref(v_arts_1310_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1333_){
_start:
{
if (lean_obj_tag(v_e_1333_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1344_; 
v_a_1335_ = lean_ctor_get(v_e_1333_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_e_1333_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1337_ = v_e_1333_;
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v_e_1333_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_io_error_to_string(v_a_1335_);
v___x_1340_ = lean_mk_io_user_error(v___x_1339_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 1);
lean_ctor_set(v___x_1337_, 0, v___x_1340_);
v___x_1342_ = v___x_1337_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
v_a_1345_ = lean_ctor_get(v_e_1333_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_e_1333_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v_e_1333_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v_e_1333_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 0);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1353_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1356_, lean_object* v_e_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1360_, lean_object* v_e_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1360_, v_e_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1364_, lean_object* v___y_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_fst_1368_; lean_object* v_snd_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1397_; 
v_fst_1368_ = lean_ctor_get(v_a_1366_, 0);
v_snd_1369_ = lean_ctor_get(v_a_1366_, 1);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_a_1366_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1371_ = v_a_1366_;
v_isShared_1372_ = v_isSharedCheck_1397_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_snd_1369_);
lean_inc(v_fst_1368_);
lean_dec(v_a_1366_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1397_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = lean_array_get_size(v_a_1364_);
v___x_1374_ = lean_nat_dec_lt(v_snd_1369_, v___x_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1376_; 
if (v_isShared_1372_ == 0)
{
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_fst_1368_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_snd_1369_);
v___x_1376_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
return v___x_1377_;
}
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1379_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1380_ = lean_array_get_borrowed(v___x_1379_, v_a_1364_, v_snd_1369_);
lean_inc(v___x_1380_);
v___x_1381_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1380_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = l_Array_append___redArg(v_fst_1368_, v_a_1382_);
lean_dec(v_a_1382_);
v___x_1384_ = lean_nat_add(v_snd_1369_, v___y_1365_);
lean_dec(v_snd_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1384_);
lean_ctor_set(v___x_1371_, 0, v___x_1383_);
v___x_1386_ = v___x_1371_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
v_a_1366_ = v___x_1386_;
goto _start;
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_del_object(v___x_1371_);
lean_dec(v_snd_1369_);
lean_dec(v_fst_1368_);
v_a_1389_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1381_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1381_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1398_, lean_object* v___y_1399_, lean_object* v_a_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1398_, v___y_1399_, v_a_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1403_, lean_object* v___y_1404_, lean_object* v___x_1405_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1403_, v___y_1404_, v___x_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1416_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1416_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_fst_1412_; lean_object* v___x_1414_; 
v_fst_1412_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_fst_1412_);
lean_dec(v_a_1408_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 1);
lean_ctor_set(v___x_1410_, 0, v_fst_1412_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_fst_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_a_1417_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1407_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1407_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 0);
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1425_, lean_object* v___y_1426_, lean_object* v___x_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1425_, v___y_1426_, v___x_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v_a_1425_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1430_, lean_object* v_a_1431_, lean_object* v___y_1432_, lean_object* v_a_1433_, lean_object* v_b_1434_){
_start:
{
uint8_t v___x_1436_; 
v___x_1436_ = lean_nat_dec_lt(v_a_1433_, v_upperBound_1430_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_dec(v_a_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v_a_1431_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_b_1434_);
return v___x_1437_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___f_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___x_1439_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1433_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
lean_ctor_set(v___x_1440_, 1, v_a_1433_);
lean_inc(v___y_1432_);
lean_inc_ref(v_a_1431_);
v___f_1441_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1441_, 0, v_a_1431_);
lean_closure_set(v___f_1441_, 1, v___y_1432_);
lean_closure_set(v___f_1441_, 2, v___x_1440_);
v___x_1442_ = lean_io_as_task(v___f_1441_, v___x_1438_);
v___x_1443_ = lean_array_push(v_b_1434_, v___x_1442_);
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = lean_nat_add(v_a_1433_, v___x_1444_);
lean_dec(v_a_1433_);
v_a_1433_ = v___x_1445_;
v_b_1434_ = v___x_1443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1447_, lean_object* v_a_1448_, lean_object* v___y_1449_, lean_object* v_a_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1447_, v_a_1448_, v___y_1449_, v_a_1450_, v_b_1451_);
lean_dec(v_upperBound_1447_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1454_, size_t v_sz_1455_, size_t v_i_1456_, lean_object* v_b_1457_){
_start:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_usize_dec_lt(v_i_1456_, v_sz_1455_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v_b_1457_);
return v___x_1460_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_a_1461_ = lean_array_uget_borrowed(v_as_1454_, v_i_1456_);
lean_inc(v_a_1461_);
v___x_1462_ = lean_task_get_own(v_a_1461_);
v___x_1463_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1462_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; size_t v___x_1466_; size_t v___x_1467_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = l_Array_append___redArg(v_b_1457_, v_a_1464_);
lean_dec(v_a_1464_);
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_add(v_i_1456_, v___x_1466_);
v_i_1456_ = v___x_1467_;
v_b_1457_ = v___x_1465_;
goto _start;
}
else
{
lean_dec_ref(v_b_1457_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1469_, lean_object* v_sz_1470_, lean_object* v_i_1471_, lean_object* v_b_1472_, lean_object* v___y_1473_){
_start:
{
size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1470_);
lean_dec(v_sz_1470_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1471_);
lean_dec(v_i_1471_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1469_, v_sz_boxed_1474_, v_i_boxed_1475_, v_b_1472_);
lean_dec_ref(v_as_1469_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1477_, size_t v_i_1478_, lean_object* v_bs_1479_){
_start:
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_usize_dec_lt(v_i_1478_, v_sz_1477_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1481_, 0, v_bs_1479_);
return v___x_1481_;
}
else
{
lean_object* v_v_1482_; lean_object* v___x_1483_; 
v_v_1482_ = lean_array_uget_borrowed(v_bs_1479_, v_i_1478_);
lean_inc(v_v_1482_);
v___x_1483_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1482_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v_bs_1479_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
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
lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v_bs_x27_1494_; size_t v___x_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v_a_1492_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1493_ = lean_unsigned_to_nat(0u);
v_bs_x27_1494_ = lean_array_uset(v_bs_1479_, v_i_1478_, v___x_1493_);
v___x_1495_ = ((size_t)1ULL);
v___x_1496_ = lean_usize_add(v_i_1478_, v___x_1495_);
v___x_1497_ = lean_array_uset(v_bs_x27_1494_, v_i_1478_, v_a_1492_);
v_i_1478_ = v___x_1496_;
v_bs_1479_ = v___x_1497_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1499_, lean_object* v_i_1500_, lean_object* v_bs_1501_){
_start:
{
size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1499_);
lean_dec(v_sz_1499_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1500_);
lean_dec(v_i_1500_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1502_, v_i_boxed_1503_, v_bs_1501_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1507_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 4)
{
lean_object* v_elems_1508_; size_t v_sz_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v_elems_1508_ = lean_ctor_get(v_x_1507_, 0);
lean_inc_ref(v_elems_1508_);
lean_dec_ref_known(v_x_1507_, 1);
v_sz_1509_ = lean_array_size(v_elems_1508_);
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1509_, v___x_1510_, v_elems_1508_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1512_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1513_ = lean_unsigned_to_nat(80u);
v___x_1514_ = l_Lean_Json_pretty(v_x_1507_, v___x_1513_);
v___x_1515_ = lean_string_append(v___x_1512_, v___x_1514_);
lean_dec_ref(v___x_1514_);
v___x_1516_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1517_ = lean_string_append(v___x_1515_, v___x_1516_);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1522_; uint32_t v___x_1523_; 
v___x_1522_ = lean_box(0);
v___x_1523_ = lean_internal_get_hardware_concurrency(v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1525_ = lean_uint32_to_nat(v___x_1524_);
return v___x_1525_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1527_ = lean_unsigned_to_nat(4u);
v___x_1528_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1529_ = lean_nat_dec_le(v___x_1528_, v___x_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v_depsFile_1533_; lean_object* v___x_1534_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1530_);
v_depsFile_1533_ = l_System_FilePath_addExtension(v_fname_1530_, v___x_1532_);
v___x_1534_ = l_IO_FS_readFile(v_depsFile_1533_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1621_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1621_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1621_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_a_1540_; lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Json_parse(v_a_1535_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; 
lean_dec_ref(v_fname_1530_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v_a_1540_ = v_a_1551_;
goto v___jp_1539_;
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1553_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1552_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; 
lean_dec_ref(v_fname_1530_);
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v_a_1540_ = v_a_1554_;
goto v___jp_1539_;
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___y_1559_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1610_; uint8_t v___x_1620_; 
lean_del_object(v___x_1537_);
lean_dec_ref(v_depsFile_1533_);
v_a_1555_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1556_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1557_ = lean_unsigned_to_nat(4u);
v___x_1620_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1620_ == 0)
{
v___y_1610_ = v___x_1557_;
goto v___jp_1609_;
}
else
{
v___y_1610_ = v___x_1556_;
goto v___jp_1609_;
}
v___jp_1558_:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1560_ = lean_mk_empty_array_with_capacity(v___y_1559_);
v___x_1561_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1555_);
lean_inc(v___y_1559_);
v___x_1562_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1559_, v_a_1555_, v___y_1559_, v___x_1561_, v___x_1560_);
lean_dec(v___y_1559_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; size_t v_sz_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = lean_array_get_size(v_a_1555_);
lean_dec(v_a_1555_);
v___x_1565_ = lean_nat_mul(v___x_1564_, v___x_1557_);
v___x_1566_ = lean_mk_empty_array_with_capacity(v___x_1565_);
lean_dec(v___x_1565_);
v_sz_1567_ = lean_array_size(v_a_1563_);
v___x_1568_ = ((size_t)0ULL);
v___x_1569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1563_, v_sz_1567_, v___x_1568_, v___x_1566_);
lean_dec(v_a_1563_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = lean_compacted_region_read(v_fname_1530_, v_a_1570_);
lean_dec(v_a_1570_);
lean_dec_ref(v_fname_1530_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_fst_1576_; lean_object* v___x_1578_; 
v_fst_1576_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_fst_1576_);
lean_dec(v_a_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v_fst_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_fst_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
v_a_1581_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1571_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1571_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_fname_1530_);
v_a_1589_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1569_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1569_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_a_1555_);
lean_dec_ref(v_fname_1530_);
v_a_1597_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1562_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1562_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
v___jp_1605_:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_nat_dec_le(v___y_1606_, v___y_1607_);
if (v___x_1608_ == 0)
{
lean_dec(v___y_1607_);
v___y_1559_ = v___y_1606_;
goto v___jp_1558_;
}
else
{
lean_dec(v___y_1606_);
v___y_1559_ = v___y_1607_;
goto v___jp_1558_;
}
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1612_ = lean_io_getenv(v___x_1611_);
v___x_1613_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1612_) == 0)
{
v___y_1606_ = v___x_1613_;
v___y_1607_ = v___y_1610_;
goto v___jp_1605_;
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_val_1614_ = lean_ctor_get(v___x_1612_, 0);
lean_inc(v_val_1614_);
lean_dec_ref_known(v___x_1612_, 1);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_string_utf8_byte_size(v_val_1614_);
v___x_1617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1617_, 0, v_val_1614_);
lean_ctor_set(v___x_1617_, 1, v___x_1615_);
lean_ctor_set(v___x_1617_, 2, v___x_1616_);
v___x_1618_ = l_String_Slice_toNat_x3f(v___x_1617_);
lean_dec_ref_known(v___x_1617_, 3);
if (lean_obj_tag(v___x_1618_) == 0)
{
v___y_1606_ = v___x_1613_;
v___y_1607_ = v___y_1610_;
goto v___jp_1605_;
}
else
{
lean_object* v_val_1619_; 
lean_dec(v___y_1610_);
v_val_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___y_1606_ = v___x_1613_;
v___y_1607_ = v_val_1619_;
goto v___jp_1605_;
}
}
}
}
}
v___jp_1539_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1548_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1542_ = lean_string_append(v___x_1541_, v_depsFile_1533_);
lean_dec_ref(v_depsFile_1533_);
v___x_1543_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1544_ = lean_string_append(v___x_1542_, v___x_1543_);
v___x_1545_ = lean_string_append(v___x_1544_, v_a_1540_);
lean_dec_ref(v_a_1540_);
v___x_1546_ = lean_mk_io_user_error(v___x_1545_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 1);
lean_ctor_set(v___x_1537_, 0, v___x_1546_);
v___x_1548_ = v___x_1537_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_depsFile_1533_);
lean_dec_ref(v_fname_1530_);
v_a_1622_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1534_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1534_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1633_, lean_object* v___y_1634_, lean_object* v_inst_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1633_, v___y_1634_, v_a_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1639_, lean_object* v___y_1640_, lean_object* v_inst_1641_, lean_object* v_a_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1639_, v___y_1640_, v_inst_1641_, v_a_1642_);
lean_dec(v___y_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1645_, lean_object* v_a_1646_, lean_object* v___y_1647_, lean_object* v_inst_1648_, lean_object* v_R_1649_, lean_object* v_a_1650_, lean_object* v_b_1651_, lean_object* v_c_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1645_, v_a_1646_, v___y_1647_, v_a_1650_, v_b_1651_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1655_, lean_object* v_a_1656_, lean_object* v___y_1657_, lean_object* v_inst_1658_, lean_object* v_R_1659_, lean_object* v_a_1660_, lean_object* v_b_1661_, lean_object* v_c_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1655_, v_a_1656_, v___y_1657_, v_inst_1658_, v_R_1659_, v_a_1660_, v_b_1661_, v_c_1662_);
lean_dec(v_upperBound_1655_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1665_, size_t v_sz_1666_, size_t v_i_1667_, lean_object* v_b_1668_){
_start:
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_usize_dec_lt(v_i_1667_, v_sz_1666_);
if (v___x_1670_ == 0)
{
return v_b_1668_;
}
else
{
lean_object* v_a_1671_; lean_object* v_cancelTk_x3f_1672_; lean_object* v___x_1673_; 
v_a_1671_ = lean_array_uget_borrowed(v_as_1665_, v_i_1667_);
v_cancelTk_x3f_1672_ = lean_ctor_get(v_a_1671_, 2);
v___x_1673_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1672_) == 1)
{
lean_object* v_val_1680_; lean_object* v___x_1681_; 
v_val_1680_ = lean_ctor_get(v_cancelTk_x3f_1672_, 0);
v___x_1681_ = l_IO_CancelToken_set(v_val_1680_);
goto v___jp_1674_;
}
else
{
goto v___jp_1674_;
}
v___jp_1674_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; size_t v___x_1677_; size_t v___x_1678_; 
lean_inc(v_a_1671_);
v___x_1675_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1671_);
v___x_1676_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1675_);
lean_dec(v___x_1675_);
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1667_, v___x_1677_);
v_i_1667_ = v___x_1678_;
v_b_1668_ = v___x_1673_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1682_){
_start:
{
lean_object* v_children_1684_; lean_object* v___x_1685_; size_t v_sz_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v_children_1684_ = lean_ctor_get(v_s_1682_, 1);
v___x_1685_ = lean_box(0);
v_sz_1686_ = lean_array_size(v_children_1684_);
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1684_, v_sz_1686_, v___x_1687_, v___x_1685_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1689_);
lean_dec_ref(v_s_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1692_, lean_object* v_sz_1693_, lean_object* v_i_1694_, lean_object* v_b_1695_, lean_object* v___y_1696_){
_start:
{
size_t v_sz_boxed_1697_; size_t v_i_boxed_1698_; lean_object* v_res_1699_; 
v_sz_boxed_1697_ = lean_unbox_usize(v_sz_1693_);
lean_dec(v_sz_1693_);
v_i_boxed_1698_ = lean_unbox_usize(v_i_1694_);
lean_dec(v_i_1694_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1692_, v_sz_boxed_1697_, v_i_boxed_1698_, v_b_1695_);
lean_dec_ref(v_as_1692_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1700_, lean_object* v_m_1701_){
_start:
{
lean_object* v_result_x3f_1702_; 
v_result_x3f_1702_ = lean_ctor_get(v_snap_1700_, 4);
lean_inc(v_result_x3f_1702_);
if (lean_obj_tag(v_result_x3f_1702_) == 1)
{
lean_object* v_val_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1801_; 
v_val_1703_ = lean_ctor_get(v_result_x3f_1702_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_result_x3f_1702_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1705_ = v_result_x3f_1702_;
v_isShared_1706_ = v_isSharedCheck_1801_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_val_1703_);
lean_dec(v_result_x3f_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1801_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_toSnapshot_1707_; lean_object* v_metaSnap_1708_; lean_object* v_ictx_1709_; lean_object* v_stx_1710_; lean_object* v_parserState_1711_; lean_object* v_processedSnap_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1800_; 
v_toSnapshot_1707_ = lean_ctor_get(v_snap_1700_, 0);
v_metaSnap_1708_ = lean_ctor_get(v_snap_1700_, 1);
v_ictx_1709_ = lean_ctor_get(v_snap_1700_, 2);
v_stx_1710_ = lean_ctor_get(v_snap_1700_, 3);
v_parserState_1711_ = lean_ctor_get(v_val_1703_, 0);
v_processedSnap_1712_ = lean_ctor_get(v_val_1703_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_val_1703_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1714_ = v_val_1703_;
v_isShared_1715_ = v_isSharedCheck_1800_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_processedSnap_1712_);
lean_inc(v_parserState_1711_);
lean_dec(v_val_1703_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1800_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_processed_1716_; lean_object* v_result_x3f_1717_; 
v_processed_1716_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1712_);
v_result_x3f_1717_ = lean_ctor_get(v_processed_1716_, 2);
lean_inc(v_result_x3f_1717_);
if (lean_obj_tag(v_result_x3f_1717_) == 1)
{
lean_object* v_val_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1799_; 
v_val_1718_ = lean_ctor_get(v_result_x3f_1717_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_result_x3f_1717_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1720_ = v_result_x3f_1717_;
v_isShared_1721_ = v_isSharedCheck_1799_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_val_1718_);
lean_dec(v_result_x3f_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1799_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v_cmdState_1722_; lean_object* v_toSnapshot_1723_; lean_object* v_metaSnap_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1797_; 
v_cmdState_1722_ = lean_ctor_get(v_val_1718_, 0);
lean_inc_ref(v_cmdState_1722_);
v_toSnapshot_1723_ = lean_ctor_get(v_processed_1716_, 0);
v_metaSnap_1724_ = lean_ctor_get(v_processed_1716_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_processed_1716_);
if (v_isSharedCheck_1797_ == 0)
{
lean_object* v_unused_1798_; 
v_unused_1798_ = lean_ctor_get(v_processed_1716_, 2);
lean_dec(v_unused_1798_);
v___x_1726_ = v_processed_1716_;
v_isShared_1727_ = v_isSharedCheck_1797_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_metaSnap_1724_);
lean_inc(v_toSnapshot_1723_);
lean_dec(v_processed_1716_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1797_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_firstCmdSnap_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1795_; 
v_firstCmdSnap_1728_ = lean_ctor_get(v_val_1718_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_val_1718_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v_val_1718_, 0);
lean_dec(v_unused_1796_);
v___x_1730_ = v_val_1718_;
v_isShared_1731_ = v_isSharedCheck_1795_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_firstCmdSnap_1728_);
lean_dec(v_val_1718_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1795_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_env_1732_; lean_object* v_messages_1733_; lean_object* v_scopes_1734_; lean_object* v_usedQuotCtxts_1735_; lean_object* v_nextMacroScope_1736_; lean_object* v_maxRecDepth_1737_; lean_object* v_ngen_1738_; lean_object* v_auxDeclNGen_1739_; lean_object* v_infoState_1740_; lean_object* v_traceState_1741_; lean_object* v_snapshotTasks_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1794_; 
v_env_1732_ = lean_ctor_get(v_cmdState_1722_, 0);
v_messages_1733_ = lean_ctor_get(v_cmdState_1722_, 1);
v_scopes_1734_ = lean_ctor_get(v_cmdState_1722_, 2);
v_usedQuotCtxts_1735_ = lean_ctor_get(v_cmdState_1722_, 3);
v_nextMacroScope_1736_ = lean_ctor_get(v_cmdState_1722_, 4);
v_maxRecDepth_1737_ = lean_ctor_get(v_cmdState_1722_, 5);
v_ngen_1738_ = lean_ctor_get(v_cmdState_1722_, 6);
v_auxDeclNGen_1739_ = lean_ctor_get(v_cmdState_1722_, 7);
v_infoState_1740_ = lean_ctor_get(v_cmdState_1722_, 8);
v_traceState_1741_ = lean_ctor_get(v_cmdState_1722_, 9);
v_snapshotTasks_1742_ = lean_ctor_get(v_cmdState_1722_, 10);
v_isSharedCheck_1794_ = !lean_is_exclusive(v_cmdState_1722_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1744_ = v_cmdState_1722_;
v_isShared_1745_ = v_isSharedCheck_1794_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snapshotTasks_1742_);
lean_inc(v_traceState_1741_);
lean_inc(v_infoState_1740_);
lean_inc(v_auxDeclNGen_1739_);
lean_inc(v_ngen_1738_);
lean_inc(v_maxRecDepth_1737_);
lean_inc(v_nextMacroScope_1736_);
lean_inc(v_usedQuotCtxts_1735_);
lean_inc(v_scopes_1734_);
lean_inc(v_messages_1733_);
lean_inc(v_env_1732_);
lean_dec(v_cmdState_1722_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1794_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v_mainModule_1747_; uint8_t v___x_1748_; 
v___x_1746_ = l_Lean_Environment_header(v_env_1732_);
v_mainModule_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_mainModule_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = lean_name_eq(v_mainModule_1747_, v_m_1701_);
lean_dec(v_mainModule_1747_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1788_; 
lean_inc(v_stx_1710_);
lean_inc_ref(v_ictx_1709_);
lean_inc_ref(v_metaSnap_1708_);
lean_inc_ref(v_toSnapshot_1707_);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_snap_1700_);
if (v_isSharedCheck_1788_ == 0)
{
lean_object* v_unused_1789_; lean_object* v_unused_1790_; lean_object* v_unused_1791_; lean_object* v_unused_1792_; lean_object* v_unused_1793_; 
v_unused_1789_ = lean_ctor_get(v_snap_1700_, 4);
lean_dec(v_unused_1789_);
v_unused_1790_ = lean_ctor_get(v_snap_1700_, 3);
lean_dec(v_unused_1790_);
v_unused_1791_ = lean_ctor_get(v_snap_1700_, 2);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_snap_1700_, 1);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_snap_1700_, 0);
lean_dec(v_unused_1793_);
v___x_1750_ = v_snap_1700_;
v_isShared_1751_ = v_isSharedCheck_1788_;
goto v_resetjp_1749_;
}
else
{
lean_dec(v_snap_1700_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1788_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_idx_1752_; lean_object* v_parentIdxs_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1786_; 
v_idx_1752_ = lean_ctor_get(v_auxDeclNGen_1739_, 1);
v_parentIdxs_1753_ = lean_ctor_get(v_auxDeclNGen_1739_, 2);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_auxDeclNGen_1739_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v_auxDeclNGen_1739_, 0);
lean_dec(v_unused_1787_);
v___x_1755_ = v_auxDeclNGen_1739_;
v_isShared_1756_ = v_isSharedCheck_1786_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_parentIdxs_1753_);
lean_inc(v_idx_1752_);
lean_dec(v_auxDeclNGen_1739_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1786_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_newEnv_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v_newEnv_1757_ = l_Lean_Environment_setMainModule(v_env_1732_, v_m_1701_);
v___x_1758_ = lean_box(0);
v___x_1759_ = l_Lean_mkPrivateName(v_newEnv_1757_, v___x_1758_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1759_);
v___x_1761_ = v___x_1755_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_idx_1752_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_parentIdxs_1753_);
v___x_1761_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v_newCmdState_1763_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 7, v___x_1761_);
lean_ctor_set(v___x_1744_, 0, v_newEnv_1757_);
v_newCmdState_1763_ = v___x_1744_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_newEnv_1757_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_messages_1733_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_scopes_1734_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_usedQuotCtxts_1735_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_nextMacroScope_1736_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v_maxRecDepth_1737_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_ngen_1738_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v_infoState_1740_);
lean_ctor_set(v_reuseFailAlloc_1784_, 9, v_traceState_1741_);
lean_ctor_set(v_reuseFailAlloc_1784_, 10, v_snapshotTasks_1742_);
v_newCmdState_1763_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v___x_1765_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v_newCmdState_1763_);
v___x_1765_ = v___x_1730_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_newCmdState_1763_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_firstCmdSnap_1728_);
v___x_1765_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
lean_object* v___x_1767_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1765_);
v___x_1767_ = v___x_1720_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v_newProcessed_1769_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 2, v___x_1767_);
v_newProcessed_1769_ = v___x_1726_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_toSnapshot_1723_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_metaSnap_1724_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v___x_1767_);
v_newProcessed_1769_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1770_, v_newProcessed_1769_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___x_1771_);
v___x_1773_ = v___x_1714_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_parserState_1711_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1773_);
v___x_1775_ = v___x_1705_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 4, v___x_1775_);
v___x_1777_ = v___x_1750_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_toSnapshot_1707_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_metaSnap_1708_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_ictx_1709_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_stx_1710_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
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
lean_del_object(v___x_1744_);
lean_dec_ref(v_snapshotTasks_1742_);
lean_dec_ref(v_traceState_1741_);
lean_dec_ref(v_infoState_1740_);
lean_dec_ref(v_auxDeclNGen_1739_);
lean_dec_ref(v_ngen_1738_);
lean_dec(v_maxRecDepth_1737_);
lean_dec(v_nextMacroScope_1736_);
lean_dec(v_usedQuotCtxts_1735_);
lean_dec(v_scopes_1734_);
lean_dec_ref(v_messages_1733_);
lean_dec_ref(v_env_1732_);
lean_del_object(v___x_1730_);
lean_dec_ref(v_firstCmdSnap_1728_);
lean_del_object(v___x_1726_);
lean_dec_ref(v_metaSnap_1724_);
lean_dec_ref(v_toSnapshot_1723_);
lean_del_object(v___x_1720_);
lean_del_object(v___x_1714_);
lean_dec_ref(v_parserState_1711_);
lean_del_object(v___x_1705_);
lean_dec(v_m_1701_);
return v_snap_1700_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1717_);
lean_dec(v_processed_1716_);
lean_del_object(v___x_1714_);
lean_dec_ref(v_parserState_1711_);
lean_del_object(v___x_1705_);
lean_dec(v_m_1701_);
return v_snap_1700_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1702_);
lean_dec(v_m_1701_);
return v_snap_1700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1808_, lean_object* v_incr_1809_, lean_object* v_res_1810_){
_start:
{
lean_object* v_cmdState_1812_; lean_object* v_env_1813_; lean_object* v_initModIdxs_1814_; lean_object* v___x_1815_; 
v_cmdState_1812_ = lean_ctor_get(v_res_1810_, 0);
lean_inc_ref(v_cmdState_1812_);
lean_dec_ref(v_res_1810_);
v_env_1813_ = lean_ctor_get(v_cmdState_1812_, 0);
lean_inc_ref(v_env_1813_);
lean_dec_ref(v_cmdState_1812_);
v_initModIdxs_1814_ = lean_ctor_get(v_incr_1809_, 1);
v___x_1815_ = l_Lean_runInitAttrsForModules(v_env_1813_, v_initModIdxs_1814_, v_opts_1808_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1816_, lean_object* v_incr_1817_, lean_object* v_res_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1816_, v_incr_1817_, v_res_1818_);
lean_dec_ref(v_incr_1817_);
lean_dec_ref(v_opts_1816_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_enable_initializer_execution();
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1828_, lean_object* v_incrFile_1829_, lean_object* v_toSave_1830_){
_start:
{
lean_object* v___x_1832_; lean_object* v_regions_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1832_ = l_Lean_Environment_header(v_env_1828_);
v_regions_1833_ = lean_ctor_get(v___x_1832_, 2);
lean_inc_ref(v_regions_1833_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1835_ = lean_box(0);
v___x_1836_ = 1;
v___x_1837_ = lean_compacted_region_save(v_incrFile_1829_, v___x_1834_, v_toSave_1830_, v_regions_1833_, v___x_1835_, v___x_1836_);
lean_dec_ref(v_regions_1833_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1838_, lean_object* v_incrFile_1839_, lean_object* v_toSave_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1838_, v_incrFile_1839_, v_toSave_1840_);
lean_dec_ref(v_toSave_1840_);
lean_dec_ref(v_incrFile_1839_);
lean_dec_ref(v_env_1838_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1843_, lean_object* v_opt_1844_){
_start:
{
lean_object* v_name_1845_; lean_object* v_map_1846_; lean_object* v___x_1847_; 
v_name_1845_ = lean_ctor_get(v_opt_1844_, 0);
v_map_1846_ = lean_ctor_get(v_opts_1843_, 0);
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1846_, v_name_1845_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_box(0);
return v___x_1848_;
}
else
{
lean_object* v_val_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1858_; 
v_val_1849_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1851_ = v___x_1847_;
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_val_1849_);
lean_dec(v___x_1847_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
if (lean_obj_tag(v_val_1849_) == 0)
{
lean_object* v_v_1853_; lean_object* v___x_1855_; 
v_v_1853_ = lean_ctor_get(v_val_1849_, 0);
lean_inc_ref(v_v_1853_);
lean_dec_ref_known(v_val_1849_, 1);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v_v_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_v_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
else
{
lean_object* v___x_1857_; 
lean_del_object(v___x_1851_);
lean_dec(v_val_1849_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1859_, lean_object* v_opt_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1859_, v_opt_1860_);
lean_dec_ref(v_opt_1860_);
lean_dec_ref(v_opts_1859_);
return v_res_1861_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1862_, lean_object* v_opt_1863_){
_start:
{
lean_object* v_name_1864_; lean_object* v_defValue_1865_; lean_object* v_map_1866_; lean_object* v___x_1867_; 
v_name_1864_ = lean_ctor_get(v_opt_1863_, 0);
v_defValue_1865_ = lean_ctor_get(v_opt_1863_, 1);
v_map_1866_ = lean_ctor_get(v_opts_1862_, 0);
v___x_1867_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1866_, v_name_1864_);
if (lean_obj_tag(v___x_1867_) == 0)
{
uint8_t v___x_1868_; 
v___x_1868_ = lean_unbox(v_defValue_1865_);
return v___x_1868_;
}
else
{
lean_object* v_val_1869_; 
v_val_1869_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___x_1867_, 1);
if (lean_obj_tag(v_val_1869_) == 1)
{
uint8_t v_v_1870_; 
v_v_1870_ = lean_ctor_get_uint8(v_val_1869_, 0);
lean_dec_ref_known(v_val_1869_, 0);
return v_v_1870_;
}
else
{
uint8_t v___x_1871_; 
lean_dec(v_val_1869_);
v___x_1871_ = lean_unbox(v_defValue_1865_);
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1872_, lean_object* v_opt_1873_){
_start:
{
uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_res_1874_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1872_, v_opt_1873_);
lean_dec_ref(v_opt_1873_);
lean_dec_ref(v_opts_1872_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_hOpt_1878_){
_start:
{
lean_inc_ref(v_hOpt_1878_);
return v_hOpt_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_hOpt_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Elab_runFrontend___lam__0(v_x_1879_, v_x_1880_, v_hOpt_1881_);
lean_dec_ref(v_hOpt_1881_);
lean_dec_ref(v_x_1880_);
lean_dec(v_x_1879_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(size_t v_sz_1883_, size_t v_i_1884_, lean_object* v_bs_1885_){
_start:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_usize_dec_lt(v_i_1884_, v_sz_1883_);
if (v___x_1886_ == 0)
{
return v_bs_1885_;
}
else
{
lean_object* v_v_1887_; lean_object* v___x_1888_; lean_object* v_bs_x27_1889_; lean_object* v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; 
v_v_1887_ = lean_array_uget(v_bs_1885_, v_i_1884_);
v___x_1888_ = lean_unsigned_to_nat(0u);
v_bs_x27_1889_ = lean_array_uset(v_bs_1885_, v_i_1884_, v___x_1888_);
v___x_1890_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1887_);
v___x_1891_ = ((size_t)1ULL);
v___x_1892_ = lean_usize_add(v_i_1884_, v___x_1891_);
v___x_1893_ = lean_array_uset(v_bs_x27_1889_, v_i_1884_, v___x_1890_);
v_i_1884_ = v___x_1892_;
v_bs_1885_ = v___x_1893_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6___boxed(lean_object* v_sz_1895_, lean_object* v_i_1896_, lean_object* v_bs_1897_){
_start:
{
size_t v_sz_boxed_1898_; size_t v_i_boxed_1899_; lean_object* v_res_1900_; 
v_sz_boxed_1898_ = lean_unbox_usize(v_sz_1895_);
lean_dec(v_sz_1895_);
v_i_boxed_1899_ = lean_unbox_usize(v_i_1896_);
lean_dec(v_i_1896_);
v_res_1900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(v_sz_boxed_1898_, v_i_boxed_1899_, v_bs_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_a_1901_){
_start:
{
size_t v_sz_1902_; size_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_sz_1902_ = lean_array_size(v_a_1901_);
v___x_1903_ = ((size_t)0ULL);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(v_sz_1902_, v___x_1903_, v_a_1901_);
v___x_1905_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_env_1906_, uint8_t v___x_1907_, lean_object* v_incrFile_1908_, lean_object* v_snapToSave_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v_regions_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1911_ = l_Lean_Environment_header(v_env_1906_);
v_regions_1912_ = lean_ctor_get(v___x_1911_, 2);
lean_inc_ref(v_regions_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l_Lean_getRegularInitAttrModIdxs(v_env_1906_);
v___x_1914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1914_, 0, v_snapToSave_1909_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_compacted_region_save(v_incrFile_1908_, v___x_1915_, v___x_1914_, v_regions_1912_, v___x_1916_, v___x_1907_);
lean_dec_ref_known(v___x_1914_, 2);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1912_);
lean_dec_ref(v_regions_1912_);
v___x_1920_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1921_ = l_System_FilePath_addExtension(v_incrFile_1908_, v___x_1920_);
v___x_1922_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3(v___x_1919_);
v___x_1923_ = l_Lean_Json_compress(v___x_1922_);
v___x_1924_ = l_IO_FS_writeFile(v___x_1921_, v___x_1923_);
lean_dec_ref(v___x_1923_);
lean_dec_ref(v___x_1921_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1932_; 
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1924_, 0);
lean_dec(v_unused_1933_);
v___x_1926_ = v___x_1924_;
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
else
{
lean_dec(v___x_1924_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1932_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_runtime_forget(v_a_1918_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1928_);
v___x_1930_ = v___x_1926_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
else
{
lean_dec(v_a_1918_);
return v___x_1924_;
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v_regions_1912_);
lean_dec_ref(v_incrFile_1908_);
v_a_1934_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1917_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1917_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_env_1942_, lean_object* v___x_1943_, lean_object* v_incrFile_1944_, lean_object* v_snapToSave_1945_, lean_object* v___y_1946_){
_start:
{
uint8_t v___x_5968__boxed_1947_; lean_object* v_res_1948_; 
v___x_5968__boxed_1947_ = lean_unbox(v___x_1943_);
v_res_1948_ = l_Lean_Elab_runFrontend___lam__1(v_env_1942_, v___x_5968__boxed_1947_, v_incrFile_1944_, v_snapToSave_1945_);
lean_dec_ref(v_env_1942_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_fileMap_1949_, lean_object* v_env_1950_, lean_object* v___x_1951_, lean_object* v_opts_1952_, lean_object* v_val_1953_, uint8_t v___x_1954_, uint8_t v_a_1955_){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = l_Lean_Linter_recordLints(v_fileMap_1949_, v_env_1950_, v___x_1951_);
v___x_1958_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1959_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1952_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_writeModule(v___x_1957_, v_val_1953_, v___x_1954_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_writeModule(v___x_1957_, v_val_1953_, v_a_1955_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_fileMap_1962_, lean_object* v_env_1963_, lean_object* v___x_1964_, lean_object* v_opts_1965_, lean_object* v_val_1966_, lean_object* v___x_1967_, lean_object* v_a_1968_, lean_object* v___y_1969_){
_start:
{
uint8_t v___x_6039__boxed_1970_; uint8_t v_a_6040__boxed_1971_; lean_object* v_res_1972_; 
v___x_6039__boxed_1970_ = lean_unbox(v___x_1967_);
v_a_6040__boxed_1971_ = lean_unbox(v_a_1968_);
v_res_1972_ = l_Lean_Elab_runFrontend___lam__2(v_fileMap_1962_, v_env_1963_, v___x_1964_, v_opts_1965_, v_val_1966_, v___x_6039__boxed_1970_, v_a_6040__boxed_1971_);
lean_dec_ref(v_opts_1965_);
lean_dec_ref(v___x_1964_);
lean_dec_ref(v_fileMap_1962_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1973_, size_t v_i_1974_, size_t v_stop_1975_, lean_object* v_b_1976_){
_start:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_usize_dec_eq(v_i_1974_, v_stop_1975_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_array_uget_borrowed(v_as_1973_, v_i_1974_);
lean_inc(v___x_1979_);
v___x_1980_ = lean_load_dynlib(v___x_1979_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; size_t v___x_1982_; size_t v___x_1983_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1982_ = ((size_t)1ULL);
v___x_1983_ = lean_usize_add(v_i_1974_, v___x_1982_);
v_i_1974_ = v___x_1983_;
v_b_1976_ = v_a_1981_;
goto _start;
}
else
{
return v___x_1980_;
}
}
else
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v_b_1976_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_1986_, lean_object* v_i_1987_, lean_object* v_stop_1988_, lean_object* v_b_1989_, lean_object* v___y_1990_){
_start:
{
size_t v_i_boxed_1991_; size_t v_stop_boxed_1992_; lean_object* v_res_1993_; 
v_i_boxed_1991_ = lean_unbox_usize(v_i_1987_);
lean_dec(v_i_1987_);
v_stop_boxed_1992_ = lean_unbox_usize(v_stop_1988_);
lean_dec(v_stop_1988_);
v_res_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_1986_, v_i_boxed_1991_, v_stop_boxed_1992_, v_b_1989_);
lean_dec_ref(v_as_1986_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_setup_x3f_1994_, lean_object* v___f_1995_, lean_object* v___x_1996_, lean_object* v_plugins_1997_, uint32_t v_trustLevel_1998_, uint8_t v___x_1999_, lean_object* v_mainModuleName_2000_, lean_object* v_stx_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; uint8_t v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; 
if (lean_obj_tag(v_setup_x3f_1994_) == 1)
{
lean_object* v_val_2018_; lean_object* v_name_2019_; lean_object* v_package_x3f_2020_; uint8_t v_isModule_2021_; lean_object* v_imports_x3f_2022_; lean_object* v_importArts_2023_; lean_object* v_dynlibs_2024_; lean_object* v_plugins_2025_; lean_object* v_options_2026_; lean_object* v___y_2033_; lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; 
lean_dec(v_mainModuleName_2000_);
v_val_2018_ = lean_ctor_get(v_setup_x3f_1994_, 0);
lean_inc(v_val_2018_);
lean_dec_ref_known(v_setup_x3f_1994_, 1);
v_name_2019_ = lean_ctor_get(v_val_2018_, 0);
lean_inc(v_name_2019_);
v_package_x3f_2020_ = lean_ctor_get(v_val_2018_, 1);
lean_inc(v_package_x3f_2020_);
v_isModule_2021_ = lean_ctor_get_uint8(v_val_2018_, sizeof(void*)*7);
v_imports_x3f_2022_ = lean_ctor_get(v_val_2018_, 2);
lean_inc(v_imports_x3f_2022_);
v_importArts_2023_ = lean_ctor_get(v_val_2018_, 3);
lean_inc(v_importArts_2023_);
v_dynlibs_2024_ = lean_ctor_get(v_val_2018_, 4);
lean_inc_ref(v_dynlibs_2024_);
v_plugins_2025_ = lean_ctor_get(v_val_2018_, 5);
lean_inc_ref(v_plugins_2025_);
v_options_2026_ = lean_ctor_get(v_val_2018_, 6);
lean_inc(v_options_2026_);
lean_dec(v_val_2018_);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_array_get_size(v_dynlibs_2024_);
v___x_2044_ = lean_nat_dec_lt(v___x_2042_, v___x_2043_);
if (v___x_2044_ == 0)
{
lean_dec_ref(v_dynlibs_2024_);
goto v___jp_2027_;
}
else
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_nat_dec_le(v___x_2043_, v___x_2043_);
if (v___x_2046_ == 0)
{
if (v___x_2044_ == 0)
{
lean_dec_ref(v_dynlibs_2024_);
goto v___jp_2027_;
}
else
{
size_t v___x_2047_; size_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = ((size_t)0ULL);
v___x_2048_ = lean_usize_of_nat(v___x_2043_);
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2024_, v___x_2047_, v___x_2048_, v___x_2045_);
lean_dec_ref(v_dynlibs_2024_);
v___y_2033_ = v___x_2049_;
goto v___jp_2032_;
}
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2043_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2024_, v___x_2050_, v___x_2051_, v___x_2045_);
lean_dec_ref(v_dynlibs_2024_);
v___y_2033_ = v___x_2052_;
goto v___jp_2032_;
}
}
v___jp_2027_:
{
uint8_t v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2001_);
v___x_2029_ = lean_strict_or(v_isModule_2021_, v___x_2028_);
if (lean_obj_tag(v_imports_x3f_2022_) == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2001_, v___x_1999_);
v___y_2005_ = v_importArts_2023_;
v___y_2006_ = v_name_2019_;
v___y_2007_ = v_plugins_2025_;
v___y_2008_ = v___x_2029_;
v___y_2009_ = v_options_2026_;
v___y_2010_ = v_package_x3f_2020_;
v___y_2011_ = v___x_2030_;
goto v___jp_2004_;
}
else
{
lean_object* v_val_2031_; 
lean_dec(v_stx_2001_);
v_val_2031_ = lean_ctor_get(v_imports_x3f_2022_, 0);
lean_inc(v_val_2031_);
lean_dec_ref_known(v_imports_x3f_2022_, 1);
v___y_2005_ = v_importArts_2023_;
v___y_2006_ = v_name_2019_;
v___y_2007_ = v_plugins_2025_;
v___y_2008_ = v___x_2029_;
v___y_2009_ = v_options_2026_;
v___y_2010_ = v_package_x3f_2020_;
v___y_2011_ = v_val_2031_;
goto v___jp_2004_;
}
}
v___jp_2032_:
{
if (lean_obj_tag(v___y_2033_) == 0)
{
lean_dec_ref_known(v___y_2033_, 1);
goto v___jp_2027_;
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_options_2026_);
lean_dec_ref(v_plugins_2025_);
lean_dec(v_importArts_2023_);
lean_dec(v_imports_x3f_2022_);
lean_dec(v_package_x3f_2020_);
lean_dec(v_name_2019_);
lean_dec(v_stx_2001_);
lean_dec_ref(v_plugins_1997_);
lean_dec_ref(v___x_1996_);
lean_dec_ref(v___f_1995_);
v_a_2034_ = lean_ctor_get(v___y_2033_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___y_2033_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___y_2033_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___y_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref(v___f_1995_);
lean_dec(v_setup_x3f_1994_);
v___x_2053_ = lean_box(0);
v___x_2054_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2001_);
v___x_2055_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2001_, v___x_1999_);
v___x_2056_ = lean_box(1);
v___x_2057_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2057_, 0, v_mainModuleName_2000_);
lean_ctor_set(v___x_2057_, 1, v___x_2053_);
lean_ctor_set(v___x_2057_, 2, v___x_2055_);
lean_ctor_set(v___x_2057_, 3, v___x_1996_);
lean_ctor_set(v___x_2057_, 4, v___x_2056_);
lean_ctor_set(v___x_2057_, 5, v_plugins_1997_);
lean_ctor_set_uint8(v___x_2057_, sizeof(void*)*6 + 4, v___x_2054_);
lean_ctor_set_uint32(v___x_2057_, sizeof(void*)*6, v_trustLevel_1998_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
return v___x_2059_;
}
v___jp_2004_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2012_ = l_Lean_LeanOptions_toOptions(v___y_2009_);
v___x_2013_ = l_Lean_Options_mergeBy(v___f_1995_, v___x_1996_, v___x_2012_);
v___x_2014_ = l_Array_append___redArg(v_plugins_1997_, v___y_2007_);
lean_dec_ref(v___y_2007_);
v___x_2015_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2015_, 0, v___y_2006_);
lean_ctor_set(v___x_2015_, 1, v___y_2010_);
lean_ctor_set(v___x_2015_, 2, v___y_2011_);
lean_ctor_set(v___x_2015_, 3, v___x_2013_);
lean_ctor_set(v___x_2015_, 4, v___y_2005_);
lean_ctor_set(v___x_2015_, 5, v___x_2014_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*6 + 4, v___y_2008_);
lean_ctor_set_uint32(v___x_2015_, sizeof(void*)*6, v_trustLevel_1998_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_setup_x3f_2060_, lean_object* v___f_2061_, lean_object* v___x_2062_, lean_object* v_plugins_2063_, lean_object* v_trustLevel_2064_, lean_object* v___x_2065_, lean_object* v_mainModuleName_2066_, lean_object* v_stx_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
uint32_t v_trustLevel_boxed_2070_; uint8_t v___x_6084__boxed_2071_; lean_object* v_res_2072_; 
v_trustLevel_boxed_2070_ = lean_unbox_uint32(v_trustLevel_2064_);
lean_dec(v_trustLevel_2064_);
v___x_6084__boxed_2071_ = lean_unbox(v___x_2065_);
v_res_2072_ = l_Lean_Elab_runFrontend___lam__3(v_setup_x3f_2060_, v___f_2061_, v___x_2062_, v_plugins_2063_, v_trustLevel_boxed_2070_, v___x_6084__boxed_2071_, v_mainModuleName_2066_, v_stx_2067_, v___y_2068_);
lean_dec_ref(v___y_2068_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_val_2073_, lean_object* v_initModIdxs_2074_, lean_object* v___x_2075_){
_start:
{
lean_object* v_cmdState_2077_; lean_object* v_env_2078_; lean_object* v___x_2079_; 
v_cmdState_2077_ = lean_ctor_get(v_val_2073_, 0);
lean_inc_ref(v_cmdState_2077_);
lean_dec_ref(v_val_2073_);
v_env_2078_ = lean_ctor_get(v_cmdState_2077_, 0);
lean_inc_ref(v_env_2078_);
lean_dec_ref(v_cmdState_2077_);
v___x_2079_ = l_Lean_runInitAttrsForModules(v_env_2078_, v_initModIdxs_2074_, v___x_2075_);
return v___x_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_val_2080_, lean_object* v_initModIdxs_2081_, lean_object* v___x_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Elab_runFrontend___lam__4(v_val_2080_, v_initModIdxs_2081_, v___x_2082_);
lean_dec_ref(v___x_2082_);
lean_dec_ref(v_initModIdxs_2081_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2088_, lean_object* v_k_2089_, uint8_t v_v_2090_){
_start:
{
lean_object* v_map_2091_; uint8_t v_hasTrace_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2106_; 
v_map_2091_ = lean_ctor_get(v_o_2088_, 0);
v_hasTrace_2092_ = lean_ctor_get_uint8(v_o_2088_, sizeof(void*)*1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_o_2088_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2094_ = v_o_2088_;
v_isShared_2095_ = v_isSharedCheck_2106_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_map_2091_);
lean_dec(v_o_2088_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2106_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2096_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2096_, 0, v_v_2090_);
lean_inc(v_k_2089_);
v___x_2097_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2089_, v___x_2096_, v_map_2091_);
if (v_hasTrace_2092_ == 0)
{
lean_object* v___x_2098_; uint8_t v___x_2099_; lean_object* v___x_2101_; 
v___x_2098_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2099_ = l_Lean_Name_isPrefixOf(v___x_2098_, v_k_2089_);
lean_dec(v_k_2089_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2097_);
v___x_2101_ = v___x_2094_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2097_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*1, v___x_2099_);
return v___x_2101_;
}
}
else
{
lean_object* v___x_2104_; 
lean_dec(v_k_2089_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2097_);
v___x_2104_ = v___x_2094_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2097_);
lean_ctor_set_uint8(v_reuseFailAlloc_2105_, sizeof(void*)*1, v_hasTrace_2092_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2107_, lean_object* v_k_2108_, lean_object* v_v_2109_){
_start:
{
uint8_t v_v_boxed_2110_; lean_object* v_res_2111_; 
v_v_boxed_2110_ = lean_unbox(v_v_2109_);
v_res_2111_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2107_, v_k_2108_, v_v_boxed_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2112_, lean_object* v_opt_2113_, uint8_t v_val_2114_){
_start:
{
lean_object* v_name_2115_; lean_object* v___x_2116_; 
v_name_2115_ = lean_ctor_get(v_opt_2113_, 0);
lean_inc(v_name_2115_);
lean_dec_ref(v_opt_2113_);
v___x_2116_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2112_, v_name_2115_, v_val_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2117_, lean_object* v_opt_2118_, lean_object* v_val_2119_){
_start:
{
uint8_t v_val_boxed_2120_; lean_object* v_res_2121_; 
v_val_boxed_2120_ = lean_unbox(v_val_2119_);
v_res_2121_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2117_, v_opt_2118_, v_val_boxed_2120_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2122_, lean_object* v_opt_2123_, uint8_t v_val_2124_){
_start:
{
lean_object* v_name_2125_; lean_object* v_map_2126_; uint8_t v___x_2127_; 
v_name_2125_ = lean_ctor_get(v_opt_2123_, 0);
v_map_2126_ = lean_ctor_get(v_opts_2122_, 0);
v___x_2127_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2125_, v_map_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2122_, v_opt_2123_, v_val_2124_);
return v___x_2128_;
}
else
{
lean_dec_ref(v_opt_2123_);
return v_opts_2122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2129_, lean_object* v_opt_2130_, lean_object* v_val_2131_){
_start:
{
uint8_t v_val_boxed_2132_; lean_object* v_res_2133_; 
v_val_boxed_2132_ = lean_unbox(v_val_2131_);
v_res_2133_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2129_, v_opt_2130_, v_val_boxed_2132_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2134_, size_t v_i_2135_, lean_object* v_bs_2136_){
_start:
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_usize_dec_lt(v_i_2135_, v_sz_2134_);
if (v___x_2137_ == 0)
{
return v_bs_2136_;
}
else
{
lean_object* v_v_2138_; lean_object* v_traces_2139_; lean_object* v___x_2140_; lean_object* v_bs_x27_2141_; size_t v___x_2142_; size_t v___x_2143_; lean_object* v___x_2144_; 
v_v_2138_ = lean_array_uget_borrowed(v_bs_2136_, v_i_2135_);
v_traces_2139_ = lean_ctor_get(v_v_2138_, 3);
lean_inc_ref(v_traces_2139_);
v___x_2140_ = lean_unsigned_to_nat(0u);
v_bs_x27_2141_ = lean_array_uset(v_bs_2136_, v_i_2135_, v___x_2140_);
v___x_2142_ = ((size_t)1ULL);
v___x_2143_ = lean_usize_add(v_i_2135_, v___x_2142_);
v___x_2144_ = lean_array_uset(v_bs_x27_2141_, v_i_2135_, v_traces_2139_);
v_i_2135_ = v___x_2143_;
v_bs_2136_ = v___x_2144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2146_, lean_object* v_i_2147_, lean_object* v_bs_2148_){
_start:
{
size_t v_sz_boxed_2149_; size_t v_i_boxed_2150_; lean_object* v_res_2151_; 
v_sz_boxed_2149_ = lean_unbox_usize(v_sz_2146_);
lean_dec(v_sz_2146_);
v_i_boxed_2150_ = lean_unbox_usize(v_i_2147_);
lean_dec(v_i_2147_);
v_res_2151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2149_, v_i_boxed_2150_, v_bs_2148_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = l_Lean_Language_Snapshot_transform(v_s_2154_, v___y_2155_);
v___x_2157_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2159_, v___y_2160_);
lean_dec_ref(v___y_2160_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___f_2165_; lean_object* v___x_2166_; 
v___f_2165_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2166_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2163_, v___f_2165_, v_a_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2167_, lean_object* v_a_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2167_, v_a_2168_);
lean_dec_ref(v_a_2168_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2174_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2171_, v___x_2173_, v_a_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2175_, v_a_2176_);
lean_dec_ref(v_a_2176_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_toSnapshot_2180_; lean_object* v_metaSnap_2181_; lean_object* v_result_x3f_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___y_2186_; 
v_toSnapshot_2180_ = lean_ctor_get(v_s_2178_, 0);
lean_inc_ref(v_toSnapshot_2180_);
v_metaSnap_2181_ = lean_ctor_get(v_s_2178_, 1);
lean_inc_ref(v_metaSnap_2181_);
v_result_x3f_2182_ = lean_ctor_get(v_s_2178_, 2);
lean_inc(v_result_x3f_2182_);
lean_dec_ref(v_s_2178_);
v___x_2183_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2180_, v___y_2179_);
v___x_2184_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2181_, v___y_2179_);
if (lean_obj_tag(v_result_x3f_2182_) == 0)
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_box(0);
v___y_2186_ = v___x_2192_;
goto v___jp_2185_;
}
else
{
lean_object* v_val_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2202_; 
v_val_2193_ = lean_ctor_get(v_result_x3f_2182_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_result_x3f_2182_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2195_ = v_result_x3f_2182_;
v_isShared_2196_ = v_isSharedCheck_2202_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_val_2193_);
lean_dec(v_result_x3f_2182_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2202_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_firstCmdSnap_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v_firstCmdSnap_2197_ = lean_ctor_get(v_val_2193_, 1);
lean_inc_ref(v_firstCmdSnap_2197_);
lean_dec(v_val_2193_);
v___x_2198_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2197_, v___y_2179_);
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 0, v___x_2198_);
v___x_2200_ = v___x_2195_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
v___y_2186_ = v___x_2200_;
goto v___jp_2185_;
}
}
}
v___jp_2185_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = lean_mk_empty_array_with_capacity(v___x_2187_);
v___x_2189_ = lean_array_push(v___x_2188_, v___x_2184_);
v___x_2190_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2186_, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2183_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
return v___x_2191_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2203_, v___y_2204_);
lean_dec_ref(v___y_2204_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v___f_2209_; lean_object* v___x_2210_; 
v___f_2209_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2210_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2207_, v___f_2209_, v_a_2208_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2211_, lean_object* v_a_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2211_, v_a_2212_);
lean_dec_ref(v_a_2212_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2214_){
_start:
{
lean_object* v_toSnapshot_2215_; lean_object* v_metaSnap_2216_; lean_object* v_result_x3f_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___y_2222_; 
v_toSnapshot_2215_ = lean_ctor_get(v_a_2214_, 0);
lean_inc_ref(v_toSnapshot_2215_);
v_metaSnap_2216_ = lean_ctor_get(v_a_2214_, 1);
lean_inc_ref(v_metaSnap_2216_);
v_result_x3f_2217_ = lean_ctor_get(v_a_2214_, 4);
lean_inc(v_result_x3f_2217_);
lean_dec_ref(v_a_2214_);
v___x_2218_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2219_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2215_, v___x_2218_);
v___x_2220_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2216_, v___x_2218_);
if (lean_obj_tag(v_result_x3f_2217_) == 0)
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_box(0);
v___y_2222_ = v___x_2228_;
goto v___jp_2221_;
}
else
{
lean_object* v_val_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2238_; 
v_val_2229_ = lean_ctor_get(v_result_x3f_2217_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_result_x3f_2217_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2231_ = v_result_x3f_2217_;
v_isShared_2232_ = v_isSharedCheck_2238_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_val_2229_);
lean_dec(v_result_x3f_2217_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2238_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_processedSnap_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v_processedSnap_2233_ = lean_ctor_get(v_val_2229_, 1);
lean_inc_ref(v_processedSnap_2233_);
lean_dec(v_val_2229_);
v___x_2234_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2233_, v___x_2218_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v___y_2222_ = v___x_2236_;
goto v___jp_2221_;
}
}
}
v___jp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = lean_mk_empty_array_with_capacity(v___x_2223_);
v___x_2225_ = lean_array_push(v___x_2224_, v___x_2220_);
v___x_2226_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2222_, v___x_2225_);
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2219_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_as_2239_, size_t v_i_2240_, size_t v_stop_2241_, lean_object* v_b_2242_){
_start:
{
uint8_t v___x_2243_; 
v___x_2243_ = lean_usize_dec_eq(v_i_2240_, v_stop_2241_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; uint8_t v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; 
v___x_2244_ = lean_array_uget_borrowed(v_as_2239_, v_i_2240_);
v___x_2245_ = 2;
v___x_2246_ = lean_box(v___x_2245_);
lean_inc(v___x_2244_);
v___x_2247_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2244_, v___x_2246_, v_b_2242_);
v___x_2248_ = ((size_t)1ULL);
v___x_2249_ = lean_usize_add(v_i_2240_, v___x_2248_);
v_i_2240_ = v___x_2249_;
v_b_2242_ = v___x_2247_;
goto _start;
}
else
{
return v_b_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8___boxed(lean_object* v_as_2251_, lean_object* v_i_2252_, lean_object* v_stop_2253_, lean_object* v_b_2254_){
_start:
{
size_t v_i_boxed_2255_; size_t v_stop_boxed_2256_; lean_object* v_res_2257_; 
v_i_boxed_2255_ = lean_unbox_usize(v_i_2252_);
lean_dec(v_i_2252_);
v_stop_boxed_2256_ = lean_unbox_usize(v_stop_2253_);
lean_dec(v_stop_2253_);
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_as_2251_, v_i_boxed_2255_, v_stop_boxed_2256_, v_b_2254_);
lean_dec_ref(v_as_2251_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2258_, size_t v_i_2259_, size_t v_stop_2260_, lean_object* v_b_2261_){
_start:
{
lean_object* v___y_2263_; uint8_t v___x_2267_; 
v___x_2267_ = lean_usize_dec_eq(v_i_2259_, v_stop_2260_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; lean_object* v_infoTree_x3f_2269_; 
v___x_2268_ = lean_array_uget_borrowed(v_as_2258_, v_i_2259_);
v_infoTree_x3f_2269_ = lean_ctor_get(v___x_2268_, 2);
if (lean_obj_tag(v_infoTree_x3f_2269_) == 1)
{
lean_object* v_val_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_val_2270_ = lean_ctor_get(v_infoTree_x3f_2269_, 0);
v___x_2271_ = lean_unsigned_to_nat(1u);
v___x_2272_ = lean_mk_empty_array_with_capacity(v___x_2271_);
lean_inc(v_val_2270_);
v___x_2273_ = lean_array_push(v___x_2272_, v_val_2270_);
v___x_2274_ = l_Array_append___redArg(v_b_2261_, v___x_2273_);
lean_dec_ref(v___x_2273_);
v___y_2263_ = v___x_2274_;
goto v___jp_2262_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2276_ = l_Array_append___redArg(v_b_2261_, v___x_2275_);
v___y_2263_ = v___x_2276_;
goto v___jp_2262_;
}
}
else
{
return v_b_2261_;
}
v___jp_2262_:
{
size_t v___x_2264_; size_t v___x_2265_; 
v___x_2264_ = ((size_t)1ULL);
v___x_2265_ = lean_usize_add(v_i_2259_, v___x_2264_);
v_i_2259_ = v___x_2265_;
v_b_2261_ = v___y_2263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2277_, lean_object* v_i_2278_, lean_object* v_stop_2279_, lean_object* v_b_2280_){
_start:
{
size_t v_i_boxed_2281_; size_t v_stop_boxed_2282_; lean_object* v_res_2283_; 
v_i_boxed_2281_ = lean_unbox_usize(v_i_2278_);
lean_dec(v_i_2278_);
v_stop_boxed_2282_ = lean_unbox_usize(v_stop_2279_);
lean_dec(v_stop_2279_);
v_res_2283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2277_, v_i_boxed_2281_, v_stop_boxed_2282_, v_b_2280_);
lean_dec_ref(v_as_2277_);
return v_res_2283_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__1(void){
_start:
{
lean_object* v___x_2285_; double v___x_2286_; 
v___x_2285_ = lean_unsigned_to_nat(1000000000u);
v___x_2286_ = lean_float_of_nat(v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2288_, lean_object* v_opts_2289_, lean_object* v_fileName_2290_, lean_object* v_mainModuleName_2291_, uint32_t v_trustLevel_2292_, lean_object* v_oleanFileName_x3f_2293_, lean_object* v_ileanFileName_x3f_2294_, uint8_t v_jsonOutput_2295_, lean_object* v_errorOnKinds_2296_, lean_object* v_plugins_2297_, uint8_t v_printStats_2298_, lean_object* v_setup_x3f_2299_, lean_object* v_incrSaveFileName_x3f_2300_, lean_object* v_incrLoadFileName_x3f_2301_, lean_object* v_incrHeaderSaveFileName_x3f_2302_){
_start:
{
lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___x_2310_; lean_object* v___f_2311_; lean_object* v___x_2312_; double v___x_2313_; double v___x_2314_; double v___x_2315_; uint8_t v___x_2316_; lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2421_; lean_object* v___y_2422_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2440_; lean_object* v___y_2441_; uint8_t v___y_2442_; lean_object* v___y_2443_; lean_object* v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; uint8_t v___y_2449_; lean_object* v___y_2472_; lean_object* v___y_2473_; uint8_t v___y_2474_; lean_object* v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; uint8_t v___y_2481_; lean_object* v___y_2492_; lean_object* v___y_2493_; uint8_t v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; uint8_t v___y_2501_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2561_; lean_object* v___y_2562_; lean_object* v_a_2563_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v___y_2584_; 
v___x_2310_ = lean_io_mono_nanos_now();
v___f_2311_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_2312_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2313_ = lean_float_of_nat(v___x_2310_);
v___x_2314_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__1, &l_Lean_Elab_runFrontend___closed__1_once, _init_l_Lean_Elab_runFrontend___closed__1);
v___x_2315_ = lean_float_div(v___x_2313_, v___x_2314_);
v___x_2316_ = 1;
v___x_2379_ = lean_string_utf8_byte_size(v_input_2288_);
v___x_2380_ = l_Lean_Parser_mkInputContext___redArg(v_input_2288_, v_fileName_2290_, v___x_2316_, v___x_2379_);
v___x_2582_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2300_) == 0)
{
v___y_2584_ = v___x_2316_;
goto v___jp_2583_;
}
else
{
uint8_t v___x_2628_; 
v___x_2628_ = 0;
v___y_2584_ = v___x_2628_;
goto v___jp_2583_;
}
v___jp_2304_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_runtime_forget(v___y_2306_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___y_2305_);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
v___jp_2317_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = l_Lean_trace_profiler_output;
v___x_2323_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2320_, v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2325_; size_t v_sz_2326_; size_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_dec_ref(v___y_2319_);
v_val_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_val_2324_);
lean_dec_ref_known(v___x_2323_, 1);
lean_inc_ref(v___y_2321_);
v___x_2325_ = l_Lean_Language_SnapshotTree_getAll(v___y_2321_);
v_sz_2326_ = lean_array_size(v___x_2325_);
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2326_, v___x_2327_, v___x_2325_);
v___x_2329_ = l_Lean_Name_toString(v_mainModuleName_2291_, v___x_2316_);
v___x_2330_ = l_Lean_Firefox_Profile_export(v___x_2329_, v___x_2315_, v___x_2328_, v___y_2320_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___x_2328_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2331_);
v___x_2333_ = l_Lean_Json_compress(v___x_2332_);
v___x_2334_ = l_IO_FS_writeFile(v_val_2324_, v___x_2333_);
lean_dec_ref(v___x_2333_);
lean_dec(v_val_2324_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
v___y_2305_ = v___y_2318_;
v___y_2306_ = v___y_2321_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v___y_2321_);
lean_dec_ref(v___y_2318_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_val_2324_);
lean_dec_ref(v___y_2321_);
lean_dec_ref(v___y_2318_);
v_a_2343_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2330_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2330_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v___x_2351_; uint8_t v___x_2352_; 
lean_dec(v___x_2323_);
v___x_2351_ = l_Lean_trace_profiler_serve;
v___x_2352_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2319_, v___x_2351_);
lean_dec_ref(v___y_2319_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v___y_2320_);
lean_dec(v_mainModuleName_2291_);
v___y_2305_ = v___y_2318_;
v___y_2306_ = v___y_2321_;
goto v___jp_2304_;
}
else
{
lean_object* v___x_2353_; size_t v_sz_2354_; size_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_inc_ref(v___y_2321_);
v___x_2353_ = l_Lean_Language_SnapshotTree_getAll(v___y_2321_);
v_sz_2354_ = lean_array_size(v___x_2353_);
v___x_2355_ = ((size_t)0ULL);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2354_, v___x_2355_, v___x_2353_);
v___x_2357_ = l_Lean_Name_toString(v_mainModuleName_2291_, v___x_2316_);
v___x_2358_ = l_Lean_Firefox_Profile_export(v___x_2357_, v___x_2315_, v___x_2356_, v___y_2320_);
lean_dec_ref(v___y_2320_);
lean_dec_ref(v___x_2356_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2359_);
v___x_2361_ = l_Lean_Json_compress(v___x_2360_);
v___x_2362_ = l_Lean_Firefox_Profile_serve(v___x_2361_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_dec_ref_known(v___x_2362_, 1);
v___y_2305_ = v___y_2318_;
v___y_2306_ = v___y_2321_;
goto v___jp_2304_;
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___y_2321_);
lean_dec_ref(v___y_2318_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
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
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v___y_2321_);
lean_dec_ref(v___y_2318_);
v_a_2371_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2358_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2358_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
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
}
v___jp_2381_:
{
lean_object* v_fileMap_2389_; uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_fst_2393_; lean_object* v_snd_2394_; lean_object* v_stx_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2415_; 
v_fileMap_2389_ = lean_ctor_get(v___x_2380_, 2);
lean_inc_ref(v_fileMap_2389_);
lean_dec_ref(v___x_2380_);
v___x_2390_ = 0;
v___x_2391_ = l_Lean_Server_findModuleRefs(v_fileMap_2389_, v___y_2388_, v___x_2390_, v___x_2390_);
lean_dec_ref(v___y_2388_);
v___x_2392_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2391_);
v_fst_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_fst_2393_);
v_snd_2394_ = lean_ctor_get(v___x_2392_, 1);
lean_inc(v_snd_2394_);
lean_dec_ref(v___x_2392_);
v_stx_2395_ = lean_ctor_get(v___y_2382_, 3);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___y_2382_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; 
v_unused_2416_ = lean_ctor_get(v___y_2382_, 4);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v___y_2382_, 2);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v___y_2382_, 1);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v___y_2382_, 0);
lean_dec(v_unused_2419_);
v___x_2397_ = v___y_2382_;
v_isShared_2398_ = v_isSharedCheck_2415_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_stx_2395_);
lean_dec(v___y_2382_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2415_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2399_ = lean_unsigned_to_nat(5u);
v___x_2400_ = l_Lean_Server_collectImports(v_stx_2395_);
lean_inc(v_mainModuleName_2291_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 4, v_snd_2394_);
lean_ctor_set(v___x_2397_, 3, v_fst_2393_);
lean_ctor_set(v___x_2397_, 2, v___x_2400_);
lean_ctor_set(v___x_2397_, 1, v_mainModuleName_2291_);
lean_ctor_set(v___x_2397_, 0, v___x_2399_);
v___x_2402_ = v___x_2397_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_mainModuleName_2291_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2414_, 3, v_fst_2393_);
lean_ctor_set(v_reuseFailAlloc_2414_, 4, v_snd_2394_);
v___x_2402_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2403_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2402_);
v___x_2404_ = l_Lean_Json_compress(v___x_2403_);
v___x_2405_ = l_IO_FS_writeFile(v___y_2383_, v___x_2404_);
lean_dec_ref(v___x_2404_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_dec_ref_known(v___x_2405_, 1);
v___y_2318_ = v___y_2384_;
v___y_2319_ = v___y_2385_;
v___y_2320_ = v___y_2386_;
v___y_2321_ = v___y_2387_;
goto v___jp_2317_;
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v_mainModuleName_2291_);
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
}
v___jp_2420_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2294_) == 1)
{
lean_object* v_val_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; uint8_t v___x_2431_; 
v_val_2427_ = lean_ctor_get(v_ileanFileName_x3f_2294_, 0);
lean_inc_ref(v___y_2426_);
v___x_2428_ = l_Lean_Language_SnapshotTree_getAll(v___y_2426_);
v___x_2429_ = lean_mk_empty_array_with_capacity(v___y_2423_);
v___x_2430_ = lean_array_get_size(v___x_2428_);
v___x_2431_ = lean_nat_dec_lt(v___y_2423_, v___x_2430_);
lean_dec(v___y_2423_);
if (v___x_2431_ == 0)
{
lean_dec_ref(v___x_2428_);
v___y_2382_ = v___y_2421_;
v___y_2383_ = v_val_2427_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___y_2424_;
v___y_2386_ = v___y_2425_;
v___y_2387_ = v___y_2426_;
v___y_2388_ = v___x_2429_;
goto v___jp_2381_;
}
else
{
uint8_t v___x_2432_; 
v___x_2432_ = lean_nat_dec_le(v___x_2430_, v___x_2430_);
if (v___x_2432_ == 0)
{
if (v___x_2431_ == 0)
{
lean_dec_ref(v___x_2428_);
v___y_2382_ = v___y_2421_;
v___y_2383_ = v_val_2427_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___y_2424_;
v___y_2386_ = v___y_2425_;
v___y_2387_ = v___y_2426_;
v___y_2388_ = v___x_2429_;
goto v___jp_2381_;
}
else
{
size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = ((size_t)0ULL);
v___x_2434_ = lean_usize_of_nat(v___x_2430_);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2428_, v___x_2433_, v___x_2434_, v___x_2429_);
lean_dec_ref(v___x_2428_);
v___y_2382_ = v___y_2421_;
v___y_2383_ = v_val_2427_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___y_2424_;
v___y_2386_ = v___y_2425_;
v___y_2387_ = v___y_2426_;
v___y_2388_ = v___x_2435_;
goto v___jp_2381_;
}
}
else
{
size_t v___x_2436_; size_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = ((size_t)0ULL);
v___x_2437_ = lean_usize_of_nat(v___x_2430_);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2428_, v___x_2436_, v___x_2437_, v___x_2429_);
lean_dec_ref(v___x_2428_);
v___y_2382_ = v___y_2421_;
v___y_2383_ = v_val_2427_;
v___y_2384_ = v___y_2422_;
v___y_2385_ = v___y_2424_;
v___y_2386_ = v___y_2425_;
v___y_2387_ = v___y_2426_;
v___y_2388_ = v___x_2438_;
goto v___jp_2381_;
}
}
}
else
{
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2421_);
lean_dec_ref(v___x_2380_);
v___y_2318_ = v___y_2422_;
v___y_2319_ = v___y_2424_;
v___y_2320_ = v___y_2425_;
v___y_2321_ = v___y_2426_;
goto v___jp_2317_;
}
}
v___jp_2439_:
{
if (v___y_2449_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2293_) == 1)
{
lean_object* v_val_2450_; lean_object* v_fileMap_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v_val_2450_ = lean_ctor_get(v_oleanFileName_x3f_2293_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v_oleanFileName_x3f_2293_, 1);
v_fileMap_2451_ = lean_ctor_get(v___x_2380_, 2);
lean_inc_ref(v_fileMap_2451_);
v___x_2452_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__2));
v___x_2453_ = lean_box(0);
v___x_2454_ = lean_mk_empty_array_with_capacity(v___y_2446_);
lean_inc_ref(v___y_2448_);
v___x_2455_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2448_, v___x_2453_, v___x_2454_);
v___x_2456_ = lean_box(v___x_2316_);
v___x_2457_ = lean_box(v___y_2442_);
v___f_2458_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2458_, 0, v_fileMap_2451_);
lean_closure_set(v___f_2458_, 1, v___y_2440_);
lean_closure_set(v___f_2458_, 2, v___x_2455_);
lean_closure_set(v___f_2458_, 3, v___y_2441_);
lean_closure_set(v___f_2458_, 4, v_val_2450_);
lean_closure_set(v___f_2458_, 5, v___x_2456_);
lean_closure_set(v___f_2458_, 6, v___x_2457_);
v___x_2459_ = lean_box(0);
v___x_2460_ = l_Lean_profileitIOUnsafe___redArg(v___x_2452_, v___y_2445_, v___f_2458_, v___x_2459_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_dec_ref_known(v___x_2460_, 1);
v___y_2421_ = v___y_2443_;
v___y_2422_ = v___y_2444_;
v___y_2423_ = v___y_2446_;
v___y_2424_ = v___y_2445_;
v___y_2425_ = v___y_2447_;
v___y_2426_ = v___y_2448_;
goto v___jp_2420_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec_ref(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___x_2380_);
lean_dec(v_mainModuleName_2291_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v_oleanFileName_x3f_2293_);
v___y_2421_ = v___y_2443_;
v___y_2422_ = v___y_2444_;
v___y_2423_ = v___y_2446_;
v___y_2424_ = v___y_2445_;
v___y_2425_ = v___y_2447_;
v___y_2426_ = v___y_2448_;
goto v___jp_2420_;
}
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec_ref(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec_ref(v___x_2380_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v___x_2469_ = lean_box(0);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
v___jp_2471_:
{
if (v_printStats_2298_ == 0)
{
v___y_2440_ = v___y_2472_;
v___y_2441_ = v___y_2473_;
v___y_2442_ = v___y_2474_;
v___y_2443_ = v___y_2475_;
v___y_2444_ = v___y_2476_;
v___y_2445_ = v___y_2478_;
v___y_2446_ = v___y_2477_;
v___y_2447_ = v___y_2479_;
v___y_2448_ = v___y_2480_;
v___y_2449_ = v___y_2481_;
goto v___jp_2439_;
}
else
{
lean_object* v___x_2482_; 
lean_inc_ref(v___y_2476_);
v___x_2482_ = l_Lean_Environment_displayStats(v___y_2476_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_dec_ref_known(v___x_2482_, 1);
v___y_2440_ = v___y_2472_;
v___y_2441_ = v___y_2473_;
v___y_2442_ = v___y_2474_;
v___y_2443_ = v___y_2475_;
v___y_2444_ = v___y_2476_;
v___y_2445_ = v___y_2478_;
v___y_2446_ = v___y_2477_;
v___y_2447_ = v___y_2479_;
v___y_2448_ = v___y_2480_;
v___y_2449_ = v___y_2481_;
goto v___jp_2439_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec_ref(v___x_2380_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2482_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2482_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
v___jp_2491_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2302_) == 1)
{
lean_object* v_val_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_val_2502_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2302_, 0);
lean_inc(v_val_2502_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2302_, 1);
lean_inc_ref(v___y_2496_);
v___x_2503_ = l_Lean_Language_Lean_truncateToHeader(v___y_2496_);
v___x_2504_ = lean_apply_3(v___y_2495_, v_val_2502_, v___x_2503_, lean_box(0));
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_dec_ref_known(v___x_2504_, 1);
lean_inc_ref(v___y_2493_);
v___y_2472_ = v___y_2492_;
v___y_2473_ = v___y_2493_;
v___y_2474_ = v___y_2494_;
v___y_2475_ = v___y_2496_;
v___y_2476_ = v___y_2497_;
v___y_2477_ = v___y_2498_;
v___y_2478_ = v___y_2493_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2500_;
v___y_2481_ = v___y_2501_;
goto v___jp_2471_;
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v___x_2380_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_dec_ref(v___y_2495_);
lean_dec(v_incrHeaderSaveFileName_x3f_2302_);
lean_inc_ref(v___y_2493_);
v___y_2472_ = v___y_2492_;
v___y_2473_ = v___y_2493_;
v___y_2474_ = v___y_2494_;
v___y_2475_ = v___y_2496_;
v___y_2476_ = v___y_2497_;
v___y_2477_ = v___y_2498_;
v___y_2478_ = v___y_2493_;
v___y_2479_ = v___y_2499_;
v___y_2480_ = v___y_2500_;
v___y_2481_ = v___y_2501_;
goto v___jp_2471_;
}
}
v___jp_2513_:
{
lean_object* v___x_2519_; 
lean_inc_ref(v___y_2517_);
v___x_2519_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2517_, v___y_2516_, v_jsonOutput_2295_, v___y_2518_);
lean_dec(v___y_2518_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2551_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2551_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2551_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; 
lean_inc_ref(v___y_2514_);
v___x_2524_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2514_);
if (lean_obj_tag(v___x_2524_) == 1)
{
lean_object* v_val_2525_; lean_object* v_env_2526_; lean_object* v_scopes_2527_; lean_object* v___x_2528_; lean_object* v_opts_2529_; lean_object* v___x_2530_; lean_object* v___f_2531_; 
lean_del_object(v___x_2522_);
v_val_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v___x_2524_, 1);
v_env_2526_ = lean_ctor_get(v_val_2525_, 0);
lean_inc_ref_n(v_env_2526_, 2);
v_scopes_2527_ = lean_ctor_get(v_val_2525_, 2);
lean_inc(v_scopes_2527_);
lean_dec(v_val_2525_);
lean_inc(v___y_2515_);
v___x_2528_ = l_List_get_x21Internal___redArg(v___x_2312_, v_scopes_2527_, v___y_2515_);
lean_dec(v_scopes_2527_);
v_opts_2529_ = lean_ctor_get(v___x_2528_, 1);
lean_inc_ref(v_opts_2529_);
lean_dec(v___x_2528_);
v___x_2530_ = lean_box(v___x_2316_);
v___f_2531_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2531_, 0, v_env_2526_);
lean_closure_set(v___f_2531_, 1, v___x_2530_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2300_) == 1)
{
lean_object* v_val_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v_val_2532_ = lean_ctor_get(v_incrSaveFileName_x3f_2300_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2300_, 1);
v___x_2533_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2517_);
lean_inc_ref(v___y_2514_);
v___x_2534_ = l_Lean_Elab_runFrontend___lam__1(v_env_2526_, v___x_2316_, v_val_2532_, v___y_2514_);
if (lean_obj_tag(v___x_2534_) == 0)
{
uint8_t v___x_2535_; uint8_t v___x_2536_; 
lean_dec_ref_known(v___x_2534_, 1);
v___x_2535_ = lean_unbox(v_a_2520_);
v___x_2536_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
lean_inc_ref(v_env_2526_);
v___y_2492_ = v_env_2526_;
v___y_2493_ = v_opts_2529_;
v___y_2494_ = v___x_2535_;
v___y_2495_ = v___f_2531_;
v___y_2496_ = v___y_2514_;
v___y_2497_ = v_env_2526_;
v___y_2498_ = v___y_2515_;
v___y_2499_ = v___y_2516_;
v___y_2500_ = v___y_2517_;
v___y_2501_ = v___x_2536_;
goto v___jp_2491_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v___f_2531_);
lean_dec_ref(v_opts_2529_);
lean_dec_ref(v_env_2526_);
lean_dec(v_a_2520_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v___x_2380_);
lean_dec(v_incrHeaderSaveFileName_x3f_2302_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v_a_2537_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2534_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2534_);
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
uint8_t v___x_2545_; uint8_t v___x_2546_; 
lean_dec(v_incrSaveFileName_x3f_2300_);
v___x_2545_ = lean_unbox(v_a_2520_);
v___x_2546_ = lean_unbox(v_a_2520_);
lean_dec(v_a_2520_);
lean_inc_ref(v_env_2526_);
v___y_2492_ = v_env_2526_;
v___y_2493_ = v_opts_2529_;
v___y_2494_ = v___x_2545_;
v___y_2495_ = v___f_2531_;
v___y_2496_ = v___y_2514_;
v___y_2497_ = v_env_2526_;
v___y_2498_ = v___y_2515_;
v___y_2499_ = v___y_2516_;
v___y_2500_ = v___y_2517_;
v___y_2501_ = v___x_2546_;
goto v___jp_2491_;
}
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_dec(v___x_2524_);
lean_dec(v_a_2520_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v___x_2380_);
lean_dec(v_incrHeaderSaveFileName_x3f_2302_);
lean_dec(v_incrSaveFileName_x3f_2300_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v___x_2547_ = lean_box(0);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 0, v___x_2547_);
v___x_2549_ = v___x_2522_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v___x_2380_);
lean_dec(v_incrHeaderSaveFileName_x3f_2302_);
lean_dec(v_incrSaveFileName_x3f_2300_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v_a_2552_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2519_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2519_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
v___jp_2560_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2564_ = l_Lean_Language_Lean_process(v___y_2561_, v_a_2563_, v___x_2380_);
lean_inc_ref(v___x_2564_);
v___x_2565_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2564_);
v___x_2566_ = lean_box(1);
v___x_2567_ = lean_unsigned_to_nat(0u);
v___x_2568_ = lean_array_get_size(v_errorOnKinds_2296_);
v___x_2569_ = lean_nat_dec_lt(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2514_ = v___x_2564_;
v___y_2515_ = v___x_2567_;
v___y_2516_ = v___y_2562_;
v___y_2517_ = v___x_2565_;
v___y_2518_ = v___x_2566_;
goto v___jp_2513_;
}
else
{
uint8_t v___x_2570_; 
v___x_2570_ = lean_nat_dec_le(v___x_2568_, v___x_2568_);
if (v___x_2570_ == 0)
{
if (v___x_2569_ == 0)
{
v___y_2514_ = v___x_2564_;
v___y_2515_ = v___x_2567_;
v___y_2516_ = v___y_2562_;
v___y_2517_ = v___x_2565_;
v___y_2518_ = v___x_2566_;
goto v___jp_2513_;
}
else
{
size_t v___x_2571_; size_t v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = ((size_t)0ULL);
v___x_2572_ = lean_usize_of_nat(v___x_2568_);
v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_errorOnKinds_2296_, v___x_2571_, v___x_2572_, v___x_2566_);
v___y_2514_ = v___x_2564_;
v___y_2515_ = v___x_2567_;
v___y_2516_ = v___y_2562_;
v___y_2517_ = v___x_2565_;
v___y_2518_ = v___x_2573_;
goto v___jp_2513_;
}
}
else
{
size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = lean_usize_of_nat(v___x_2568_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_errorOnKinds_2296_, v___x_2574_, v___x_2575_, v___x_2566_);
v___y_2514_ = v___x_2564_;
v___y_2515_ = v___x_2567_;
v___y_2516_ = v___y_2562_;
v___y_2517_ = v___x_2565_;
v___y_2518_ = v___x_2576_;
goto v___jp_2513_;
}
}
}
v___jp_2577_:
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2580_);
v___y_2561_ = v___y_2578_;
v___y_2562_ = v___y_2579_;
v_a_2563_ = v___x_2581_;
goto v___jp_2560_;
}
v___jp_2583_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___f_2590_; 
v___x_2585_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2289_, v___x_2582_, v___y_2584_);
v___x_2586_ = l_Lean_Elab_async;
v___x_2587_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2585_, v___x_2586_, v___x_2316_);
v___x_2588_ = lean_box_uint32(v_trustLevel_2292_);
v___x_2589_ = lean_box(v___x_2316_);
lean_inc(v_mainModuleName_2291_);
lean_inc_ref(v___x_2587_);
v___f_2590_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 10, 7);
lean_closure_set(v___f_2590_, 0, v_setup_x3f_2299_);
lean_closure_set(v___f_2590_, 1, v___f_2311_);
lean_closure_set(v___f_2590_, 2, v___x_2587_);
lean_closure_set(v___f_2590_, 3, v_plugins_2297_);
lean_closure_set(v___f_2590_, 4, v___x_2588_);
lean_closure_set(v___f_2590_, 5, v___x_2589_);
lean_closure_set(v___f_2590_, 6, v_mainModuleName_2291_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2301_) == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_box(0);
v___y_2561_ = v___f_2590_;
v___y_2562_ = v___x_2587_;
v_a_2563_ = v___x_2591_;
goto v___jp_2560_;
}
else
{
lean_object* v_val_2592_; lean_object* v___x_2593_; 
v_val_2592_ = lean_ctor_get(v_incrLoadFileName_x3f_2301_, 0);
lean_inc(v_val_2592_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2301_, 1);
v___x_2593_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2592_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v_snap_2595_; lean_object* v_initModIdxs_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v_snap_2595_ = lean_ctor_get(v_a_2594_, 0);
lean_inc_ref(v_snap_2595_);
v_initModIdxs_2596_ = lean_ctor_get(v_a_2594_, 1);
lean_inc_ref(v_initModIdxs_2596_);
lean_dec(v_a_2594_);
lean_inc(v_mainModuleName_2291_);
v___x_2597_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2595_, v_mainModuleName_2291_);
lean_inc_ref(v___x_2597_);
v___x_2598_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2597_);
v___x_2599_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2598_);
if (lean_obj_tag(v___x_2599_) == 1)
{
lean_object* v_val_2600_; lean_object* v___f_2601_; lean_object* v___x_2602_; 
v_val_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_val_2600_);
lean_dec_ref_known(v___x_2599_, 1);
lean_inc_ref(v___x_2587_);
v___f_2601_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2601_, 0, v_val_2600_);
lean_closure_set(v___f_2601_, 1, v_initModIdxs_2596_);
lean_closure_set(v___f_2601_, 2, v___x_2587_);
v___x_2602_ = l_Lean_withImporting___redArg(v___f_2601_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v___x_2603_; 
lean_dec_ref_known(v___x_2602_, 1);
v___x_2603_ = lean_enable_initializer_execution();
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_dec_ref_known(v___x_2603_, 1);
v___y_2578_ = v___f_2590_;
v___y_2579_ = v___x_2587_;
v_a_2580_ = v___x_2597_;
goto v___jp_2577_;
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2590_);
lean_dec_ref(v___x_2587_);
lean_dec_ref(v___x_2380_);
lean_dec(v_incrHeaderSaveFileName_x3f_2302_);
lean_dec(v_incrSaveFileName_x3f_2300_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v___x_2597_);
lean_dec_ref(v___f_2590_);
lean_dec_ref(v___x_2587_);
lean_dec_ref(v___x_2380_);
lean_dec(v_incrHeaderSaveFileName_x3f_2302_);
lean_dec(v_incrSaveFileName_x3f_2300_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v_a_2612_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2602_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2602_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
else
{
lean_dec(v___x_2599_);
lean_dec_ref(v_initModIdxs_2596_);
v___y_2578_ = v___f_2590_;
v___y_2579_ = v___x_2587_;
v_a_2580_ = v___x_2597_;
goto v___jp_2577_;
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v___f_2590_);
lean_dec_ref(v___x_2587_);
lean_dec_ref(v___x_2380_);
lean_dec(v_incrHeaderSaveFileName_x3f_2302_);
lean_dec(v_incrSaveFileName_x3f_2300_);
lean_dec(v_oleanFileName_x3f_2293_);
lean_dec(v_mainModuleName_2291_);
v_a_2620_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2593_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2593_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2629_, lean_object* v_opts_2630_, lean_object* v_fileName_2631_, lean_object* v_mainModuleName_2632_, lean_object* v_trustLevel_2633_, lean_object* v_oleanFileName_x3f_2634_, lean_object* v_ileanFileName_x3f_2635_, lean_object* v_jsonOutput_2636_, lean_object* v_errorOnKinds_2637_, lean_object* v_plugins_2638_, lean_object* v_printStats_2639_, lean_object* v_setup_x3f_2640_, lean_object* v_incrSaveFileName_x3f_2641_, lean_object* v_incrLoadFileName_x3f_2642_, lean_object* v_incrHeaderSaveFileName_x3f_2643_, lean_object* v_a_2644_){
_start:
{
uint32_t v_trustLevel_boxed_2645_; uint8_t v_jsonOutput_boxed_2646_; uint8_t v_printStats_boxed_2647_; lean_object* v_res_2648_; 
v_trustLevel_boxed_2645_ = lean_unbox_uint32(v_trustLevel_2633_);
lean_dec(v_trustLevel_2633_);
v_jsonOutput_boxed_2646_ = lean_unbox(v_jsonOutput_2636_);
v_printStats_boxed_2647_ = lean_unbox(v_printStats_2639_);
v_res_2648_ = l_Lean_Elab_runFrontend(v_input_2629_, v_opts_2630_, v_fileName_2631_, v_mainModuleName_2632_, v_trustLevel_boxed_2645_, v_oleanFileName_x3f_2634_, v_ileanFileName_x3f_2635_, v_jsonOutput_boxed_2646_, v_errorOnKinds_2637_, v_plugins_2638_, v_printStats_boxed_2647_, v_setup_x3f_2640_, v_incrSaveFileName_x3f_2641_, v_incrLoadFileName_x3f_2642_, v_incrHeaderSaveFileName_x3f_2643_);
lean_dec_ref(v_errorOnKinds_2637_);
lean_dec(v_ileanFileName_x3f_2635_);
return v_res_2648_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
