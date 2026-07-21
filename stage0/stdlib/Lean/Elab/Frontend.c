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
v___x_302_ = lean_st_ref_set(v_a_274_, v___x_301_);
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
v___x_387_ = lean_st_ref_set(v_a_352_, v___x_386_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t v_sz_485_, size_t v_i_486_, lean_object* v_bs_487_){
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
lean_object* v_v_489_; lean_object* v_diagnostics_490_; lean_object* v_msgLog_491_; lean_object* v___x_492_; lean_object* v_bs_x27_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v_v_489_ = lean_array_uget_borrowed(v_bs_487_, v_i_486_);
v_diagnostics_490_ = lean_ctor_get(v_v_489_, 1);
v_msgLog_491_ = lean_ctor_get(v_diagnostics_490_, 0);
lean_inc_ref(v_msgLog_491_);
v___x_492_ = lean_unsigned_to_nat(0u);
v_bs_x27_493_ = lean_array_uset(v_bs_487_, v_i_486_, v___x_492_);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_add(v_i_486_, v___x_494_);
v___x_496_ = lean_array_uset(v_bs_x27_493_, v_i_486_, v_msgLog_491_);
v_i_486_ = v___x_495_;
v_bs_487_ = v___x_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_sz_498_, lean_object* v_i_499_, lean_object* v_bs_500_){
_start:
{
size_t v_sz_boxed_501_; size_t v_i_boxed_502_; lean_object* v_res_503_; 
v_sz_boxed_501_ = lean_unbox_usize(v_sz_498_);
lean_dec(v_sz_498_);
v_i_boxed_502_ = lean_unbox_usize(v_i_499_);
lean_dec(v_i_499_);
v_res_503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_boxed_501_, v_i_boxed_502_, v_bs_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_504_, size_t v_i_505_, lean_object* v_bs_506_){
_start:
{
uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_lt(v_i_505_, v_sz_504_);
if (v___x_507_ == 0)
{
return v_bs_506_;
}
else
{
lean_object* v_v_508_; lean_object* v_elabSnap_509_; lean_object* v_infoTreeSnap_510_; lean_object* v___x_511_; lean_object* v_infoTree_x3f_512_; lean_object* v___x_513_; lean_object* v_bs_x27_514_; size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v_v_508_ = lean_array_uget_borrowed(v_bs_506_, v_i_505_);
v_elabSnap_509_ = lean_ctor_get(v_v_508_, 3);
v_infoTreeSnap_510_ = lean_ctor_get(v_elabSnap_509_, 3);
lean_inc_ref(v_infoTreeSnap_510_);
v___x_511_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_510_);
v_infoTree_x3f_512_ = lean_ctor_get(v___x_511_, 2);
lean_inc(v_infoTree_x3f_512_);
lean_dec(v___x_511_);
v___x_513_ = lean_unsigned_to_nat(0u);
v_bs_x27_514_ = lean_array_uset(v_bs_506_, v_i_505_, v___x_513_);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_add(v_i_505_, v___x_515_);
v___x_517_ = lean_array_uset(v_bs_x27_514_, v_i_505_, v_infoTree_x3f_512_);
v_i_505_ = v___x_516_;
v_bs_506_ = v___x_517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_519_, lean_object* v_i_520_, lean_object* v_bs_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_519_);
lean_dec(v_sz_519_);
v_i_boxed_523_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_522_, v_i_boxed_523_, v_bs_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_525_, size_t v_i_526_, lean_object* v_bs_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_lt(v_i_526_, v_sz_525_);
if (v___x_528_ == 0)
{
return v_bs_527_;
}
else
{
lean_object* v_v_529_; lean_object* v_stx_530_; lean_object* v___x_531_; lean_object* v_bs_x27_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v_v_529_ = lean_array_uget_borrowed(v_bs_527_, v_i_526_);
v_stx_530_ = lean_ctor_get(v_v_529_, 1);
lean_inc(v_stx_530_);
v___x_531_ = lean_unsigned_to_nat(0u);
v_bs_x27_532_ = lean_array_uset(v_bs_527_, v_i_526_, v___x_531_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_add(v_i_526_, v___x_533_);
v___x_535_ = lean_array_uset(v_bs_x27_532_, v_i_526_, v_stx_530_);
v_i_526_ = v___x_534_;
v_bs_527_ = v___x_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_bs_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_541_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_540_, v_i_boxed_541_, v_bs_539_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_lean_x3f_785_; lean_object* v_olean_x3f_786_; lean_object* v_oleanServer_x3f_787_; lean_object* v_ilean_x3f_788_; lean_object* v_irSig_x3f_789_; lean_object* v_ir_x3f_790_; lean_object* v_c_x3f_791_; lean_object* v_bc_x3f_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_lean_x3f_785_ = lean_ctor_get(v_a_784_, 0);
v_olean_x3f_786_ = lean_ctor_get(v_a_784_, 1);
v_oleanServer_x3f_787_ = lean_ctor_get(v_a_784_, 2);
v_ilean_x3f_788_ = lean_ctor_get(v_a_784_, 4);
v_irSig_x3f_789_ = lean_ctor_get(v_a_784_, 5);
v_ir_x3f_790_ = lean_ctor_get(v_a_784_, 6);
v_c_x3f_791_ = lean_ctor_get(v_a_784_, 7);
v_bc_x3f_792_ = lean_ctor_get(v_a_784_, 8);
v_isSharedCheck_800_ = !lean_is_exclusive(v_a_784_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v_a_784_, 3);
lean_dec(v_unused_801_);
v___x_794_ = v_a_784_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_bc_x3f_792_);
lean_inc(v_c_x3f_791_);
lean_inc(v_ir_x3f_790_);
lean_inc(v_irSig_x3f_789_);
lean_inc(v_ilean_x3f_788_);
lean_inc(v_oleanServer_x3f_787_);
lean_inc(v_olean_x3f_786_);
lean_inc(v_lean_x3f_785_);
lean_dec(v_a_784_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_filePath_783_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 3, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_lean_x3f_785_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_olean_x3f_786_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v_oleanServer_x3f_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_ilean_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 5, v_irSig_x3f_789_);
lean_ctor_set(v_reuseFailAlloc_799_, 6, v_ir_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_799_, 7, v_c_x3f_791_);
lean_ctor_set(v_reuseFailAlloc_799_, 8, v_bc_x3f_792_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_lean_x3f_804_; lean_object* v_olean_x3f_805_; lean_object* v_oleanServer_x3f_806_; lean_object* v_oleanPrivate_x3f_807_; lean_object* v_ilean_x3f_808_; lean_object* v_ir_x3f_809_; lean_object* v_c_x3f_810_; lean_object* v_bc_x3f_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_819_; 
v_lean_x3f_804_ = lean_ctor_get(v_a_803_, 0);
v_olean_x3f_805_ = lean_ctor_get(v_a_803_, 1);
v_oleanServer_x3f_806_ = lean_ctor_get(v_a_803_, 2);
v_oleanPrivate_x3f_807_ = lean_ctor_get(v_a_803_, 3);
v_ilean_x3f_808_ = lean_ctor_get(v_a_803_, 4);
v_ir_x3f_809_ = lean_ctor_get(v_a_803_, 6);
v_c_x3f_810_ = lean_ctor_get(v_a_803_, 7);
v_bc_x3f_811_ = lean_ctor_get(v_a_803_, 8);
v_isSharedCheck_819_ = !lean_is_exclusive(v_a_803_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_a_803_, 5);
lean_dec(v_unused_820_);
v___x_813_ = v_a_803_;
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_bc_x3f_811_);
lean_inc(v_c_x3f_810_);
lean_inc(v_ir_x3f_809_);
lean_inc(v_ilean_x3f_808_);
lean_inc(v_oleanPrivate_x3f_807_);
lean_inc(v_oleanServer_x3f_806_);
lean_inc(v_olean_x3f_805_);
lean_inc(v_lean_x3f_804_);
lean_dec(v_a_803_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_819_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_filePath_802_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 5, v___x_815_);
v___x_817_ = v___x_813_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_lean_x3f_804_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_olean_x3f_805_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_oleanServer_x3f_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_oleanPrivate_x3f_807_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_ilean_x3f_808_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_818_, 6, v_ir_x3f_809_);
lean_ctor_set(v_reuseFailAlloc_818_, 7, v_c_x3f_810_);
lean_ctor_set(v_reuseFailAlloc_818_, 8, v_bc_x3f_811_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_lean_x3f_823_; lean_object* v_olean_x3f_824_; lean_object* v_oleanPrivate_x3f_825_; lean_object* v_ilean_x3f_826_; lean_object* v_irSig_x3f_827_; lean_object* v_ir_x3f_828_; lean_object* v_c_x3f_829_; lean_object* v_bc_x3f_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_lean_x3f_823_ = lean_ctor_get(v_a_822_, 0);
v_olean_x3f_824_ = lean_ctor_get(v_a_822_, 1);
v_oleanPrivate_x3f_825_ = lean_ctor_get(v_a_822_, 3);
v_ilean_x3f_826_ = lean_ctor_get(v_a_822_, 4);
v_irSig_x3f_827_ = lean_ctor_get(v_a_822_, 5);
v_ir_x3f_828_ = lean_ctor_get(v_a_822_, 6);
v_c_x3f_829_ = lean_ctor_get(v_a_822_, 7);
v_bc_x3f_830_ = lean_ctor_get(v_a_822_, 8);
v_isSharedCheck_838_ = !lean_is_exclusive(v_a_822_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_a_822_, 2);
lean_dec(v_unused_839_);
v___x_832_ = v_a_822_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_bc_x3f_830_);
lean_inc(v_c_x3f_829_);
lean_inc(v_ir_x3f_828_);
lean_inc(v_irSig_x3f_827_);
lean_inc(v_ilean_x3f_826_);
lean_inc(v_oleanPrivate_x3f_825_);
lean_inc(v_olean_x3f_824_);
lean_inc(v_lean_x3f_823_);
lean_dec(v_a_822_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_filePath_821_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 2, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_lean_x3f_823_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_olean_x3f_824_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v___x_834_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_oleanPrivate_x3f_825_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v_ilean_x3f_826_);
lean_ctor_set(v_reuseFailAlloc_837_, 5, v_irSig_x3f_827_);
lean_ctor_set(v_reuseFailAlloc_837_, 6, v_ir_x3f_828_);
lean_ctor_set(v_reuseFailAlloc_837_, 7, v_c_x3f_829_);
lean_ctor_set(v_reuseFailAlloc_837_, 8, v_bc_x3f_830_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
uint8_t v___x_842_; 
v___x_842_ = 0;
return v___x_842_;
}
else
{
lean_object* v_key_843_; lean_object* v_tail_844_; uint8_t v___x_845_; 
v_key_843_ = lean_ctor_get(v_x_841_, 0);
v_tail_844_ = lean_ctor_get(v_x_841_, 2);
v___x_845_ = lean_string_dec_eq(v_key_843_, v_a_840_);
if (v___x_845_ == 0)
{
v_x_841_ = v_tail_844_;
goto _start;
}
else
{
return v___x_845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_847_, lean_object* v_x_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_847_, v_x_848_);
lean_dec(v_x_848_);
lean_dec_ref(v_a_847_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_buckets_853_; lean_object* v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v_fold_858_; uint64_t v___x_859_; uint64_t v___x_860_; uint64_t v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_buckets_853_ = lean_ctor_get(v_m_851_, 1);
v___x_854_ = lean_array_get_size(v_buckets_853_);
v___x_855_ = lean_string_hash(v_a_852_);
v___x_856_ = 32ULL;
v___x_857_ = lean_uint64_shift_right(v___x_855_, v___x_856_);
v_fold_858_ = lean_uint64_xor(v___x_855_, v___x_857_);
v___x_859_ = 16ULL;
v___x_860_ = lean_uint64_shift_right(v_fold_858_, v___x_859_);
v___x_861_ = lean_uint64_xor(v_fold_858_, v___x_860_);
v___x_862_ = lean_uint64_to_usize(v___x_861_);
v___x_863_ = lean_usize_of_nat(v___x_854_);
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_sub(v___x_863_, v___x_864_);
v___x_866_ = lean_usize_land(v___x_862_, v___x_865_);
v___x_867_ = lean_array_uget_borrowed(v_buckets_853_, v___x_866_);
v___x_868_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_852_, v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_869_, lean_object* v_a_870_){
_start:
{
uint8_t v_res_871_; lean_object* v_r_872_; 
v_res_871_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_869_, v_a_870_);
lean_dec_ref(v_a_870_);
lean_dec_ref(v_m_869_);
v_r_872_ = lean_box(v_res_871_);
return v_r_872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_873_, lean_object* v_fallback_874_, lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
lean_inc(v_fallback_874_);
return v_fallback_874_;
}
else
{
lean_object* v_key_876_; lean_object* v_value_877_; lean_object* v_tail_878_; uint8_t v___x_879_; 
v_key_876_ = lean_ctor_get(v_x_875_, 0);
v_value_877_ = lean_ctor_get(v_x_875_, 1);
v_tail_878_ = lean_ctor_get(v_x_875_, 2);
v___x_879_ = lean_string_dec_eq(v_key_876_, v_a_873_);
if (v___x_879_ == 0)
{
v_x_875_ = v_tail_878_;
goto _start;
}
else
{
lean_inc(v_value_877_);
return v_value_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_881_, lean_object* v_fallback_882_, lean_object* v_x_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_881_, v_fallback_882_, v_x_883_);
lean_dec(v_x_883_);
lean_dec(v_fallback_882_);
lean_dec_ref(v_a_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_885_, lean_object* v_a_886_, lean_object* v_fallback_887_){
_start:
{
lean_object* v_buckets_888_; lean_object* v___x_889_; uint64_t v___x_890_; uint64_t v___x_891_; uint64_t v___x_892_; uint64_t v_fold_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_buckets_888_ = lean_ctor_get(v_m_885_, 1);
v___x_889_ = lean_array_get_size(v_buckets_888_);
v___x_890_ = lean_string_hash(v_a_886_);
v___x_891_ = 32ULL;
v___x_892_ = lean_uint64_shift_right(v___x_890_, v___x_891_);
v_fold_893_ = lean_uint64_xor(v___x_890_, v___x_892_);
v___x_894_ = 16ULL;
v___x_895_ = lean_uint64_shift_right(v_fold_893_, v___x_894_);
v___x_896_ = lean_uint64_xor(v_fold_893_, v___x_895_);
v___x_897_ = lean_uint64_to_usize(v___x_896_);
v___x_898_ = lean_usize_of_nat(v___x_889_);
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_sub(v___x_898_, v___x_899_);
v___x_901_ = lean_usize_land(v___x_897_, v___x_900_);
v___x_902_ = lean_array_uget_borrowed(v_buckets_888_, v___x_901_);
v___x_903_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_886_, v_fallback_887_, v___x_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_904_, lean_object* v_a_905_, lean_object* v_fallback_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_904_, v_a_905_, v_fallback_906_);
lean_dec(v_fallback_906_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_m_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_lean_x3f_910_; lean_object* v_olean_x3f_911_; lean_object* v_oleanServer_x3f_912_; lean_object* v_oleanPrivate_x3f_913_; lean_object* v_ilean_x3f_914_; lean_object* v_irSig_x3f_915_; lean_object* v_c_x3f_916_; lean_object* v_bc_x3f_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_925_; 
v_lean_x3f_910_ = lean_ctor_get(v_a_909_, 0);
v_olean_x3f_911_ = lean_ctor_get(v_a_909_, 1);
v_oleanServer_x3f_912_ = lean_ctor_get(v_a_909_, 2);
v_oleanPrivate_x3f_913_ = lean_ctor_get(v_a_909_, 3);
v_ilean_x3f_914_ = lean_ctor_get(v_a_909_, 4);
v_irSig_x3f_915_ = lean_ctor_get(v_a_909_, 5);
v_c_x3f_916_ = lean_ctor_get(v_a_909_, 7);
v_bc_x3f_917_ = lean_ctor_get(v_a_909_, 8);
v_isSharedCheck_925_ = !lean_is_exclusive(v_a_909_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v_a_909_, 6);
lean_dec(v_unused_926_);
v___x_919_ = v_a_909_;
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_bc_x3f_917_);
lean_inc(v_c_x3f_916_);
lean_inc(v_irSig_x3f_915_);
lean_inc(v_ilean_x3f_914_);
lean_inc(v_oleanPrivate_x3f_913_);
lean_inc(v_oleanServer_x3f_912_);
lean_inc(v_olean_x3f_911_);
lean_inc(v_lean_x3f_910_);
lean_dec(v_a_909_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_925_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v_filePath_908_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 6, v___x_921_);
v___x_923_ = v___x_919_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_lean_x3f_910_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_olean_x3f_911_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_oleanServer_x3f_912_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_oleanPrivate_x3f_913_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v_ilean_x3f_914_);
lean_ctor_set(v_reuseFailAlloc_924_, 5, v_irSig_x3f_915_);
lean_ctor_set(v_reuseFailAlloc_924_, 6, v___x_921_);
lean_ctor_set(v_reuseFailAlloc_924_, 7, v_c_x3f_916_);
lean_ctor_set(v_reuseFailAlloc_924_, 8, v_bc_x3f_917_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_lean_x3f_929_; lean_object* v_oleanServer_x3f_930_; lean_object* v_oleanPrivate_x3f_931_; lean_object* v_ilean_x3f_932_; lean_object* v_irSig_x3f_933_; lean_object* v_ir_x3f_934_; lean_object* v_c_x3f_935_; lean_object* v_bc_x3f_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
v_lean_x3f_929_ = lean_ctor_get(v_a_928_, 0);
v_oleanServer_x3f_930_ = lean_ctor_get(v_a_928_, 2);
v_oleanPrivate_x3f_931_ = lean_ctor_get(v_a_928_, 3);
v_ilean_x3f_932_ = lean_ctor_get(v_a_928_, 4);
v_irSig_x3f_933_ = lean_ctor_get(v_a_928_, 5);
v_ir_x3f_934_ = lean_ctor_get(v_a_928_, 6);
v_c_x3f_935_ = lean_ctor_get(v_a_928_, 7);
v_bc_x3f_936_ = lean_ctor_get(v_a_928_, 8);
v_isSharedCheck_944_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_a_928_, 1);
lean_dec(v_unused_945_);
v___x_938_ = v_a_928_;
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_bc_x3f_936_);
lean_inc(v_c_x3f_935_);
lean_inc(v_ir_x3f_934_);
lean_inc(v_irSig_x3f_933_);
lean_inc(v_ilean_x3f_932_);
lean_inc(v_oleanPrivate_x3f_931_);
lean_inc(v_oleanServer_x3f_930_);
lean_inc(v_lean_x3f_929_);
lean_dec(v_a_928_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_940_, 0, v_filePath_927_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_lean_x3f_929_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_oleanServer_x3f_930_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_oleanPrivate_x3f_931_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_ilean_x3f_932_);
lean_ctor_set(v_reuseFailAlloc_943_, 5, v_irSig_x3f_933_);
lean_ctor_set(v_reuseFailAlloc_943_, 6, v_ir_x3f_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 7, v_c_x3f_935_);
lean_ctor_set(v_reuseFailAlloc_943_, 8, v_bc_x3f_936_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_946_, lean_object* v_b_947_, lean_object* v_x_948_){
_start:
{
if (lean_obj_tag(v_x_948_) == 0)
{
lean_dec(v_b_947_);
lean_dec_ref(v_a_946_);
return v_x_948_;
}
else
{
lean_object* v_key_949_; lean_object* v_value_950_; lean_object* v_tail_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_963_; 
v_key_949_ = lean_ctor_get(v_x_948_, 0);
v_value_950_ = lean_ctor_get(v_x_948_, 1);
v_tail_951_ = lean_ctor_get(v_x_948_, 2);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_948_);
if (v_isSharedCheck_963_ == 0)
{
v___x_953_ = v_x_948_;
v_isShared_954_ = v_isSharedCheck_963_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_tail_951_);
lean_inc(v_value_950_);
lean_inc(v_key_949_);
lean_dec(v_x_948_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_963_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = lean_string_dec_eq(v_key_949_, v_a_946_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_946_, v_b_947_, v_tail_951_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 2, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_key_949_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_value_950_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v___x_961_; 
lean_dec(v_value_950_);
lean_dec(v_key_949_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v_b_947_);
lean_ctor_set(v___x_953_, 0, v_a_946_);
v___x_961_ = v___x_953_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_946_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_b_947_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_tail_951_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
return v_x_964_;
}
else
{
lean_object* v_key_966_; lean_object* v_value_967_; lean_object* v_tail_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_991_; 
v_key_966_ = lean_ctor_get(v_x_965_, 0);
v_value_967_ = lean_ctor_get(v_x_965_, 1);
v_tail_968_ = lean_ctor_get(v_x_965_, 2);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_965_);
if (v_isSharedCheck_991_ == 0)
{
v___x_970_ = v_x_965_;
v_isShared_971_ = v_isSharedCheck_991_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_tail_968_);
lean_inc(v_value_967_);
lean_inc(v_key_966_);
lean_dec(v_x_965_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_991_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; uint64_t v___x_973_; uint64_t v___x_974_; uint64_t v___x_975_; uint64_t v_fold_976_; uint64_t v___x_977_; uint64_t v___x_978_; uint64_t v___x_979_; size_t v___x_980_; size_t v___x_981_; size_t v___x_982_; size_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_972_ = lean_array_get_size(v_x_964_);
v___x_973_ = lean_string_hash(v_key_966_);
v___x_974_ = 32ULL;
v___x_975_ = lean_uint64_shift_right(v___x_973_, v___x_974_);
v_fold_976_ = lean_uint64_xor(v___x_973_, v___x_975_);
v___x_977_ = 16ULL;
v___x_978_ = lean_uint64_shift_right(v_fold_976_, v___x_977_);
v___x_979_ = lean_uint64_xor(v_fold_976_, v___x_978_);
v___x_980_ = lean_uint64_to_usize(v___x_979_);
v___x_981_ = lean_usize_of_nat(v___x_972_);
v___x_982_ = ((size_t)1ULL);
v___x_983_ = lean_usize_sub(v___x_981_, v___x_982_);
v___x_984_ = lean_usize_land(v___x_980_, v___x_983_);
v___x_985_ = lean_array_uget_borrowed(v_x_964_, v___x_984_);
lean_inc(v___x_985_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 2, v___x_985_);
v___x_987_ = v___x_970_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_key_966_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_value_967_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v___x_985_);
v___x_987_ = v_reuseFailAlloc_990_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; 
v___x_988_ = lean_array_uset(v_x_964_, v___x_984_, v___x_987_);
v_x_964_ = v___x_988_;
v_x_965_ = v_tail_968_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_992_, lean_object* v_source_993_, lean_object* v_target_994_){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = lean_array_get_size(v_source_993_);
v___x_996_ = lean_nat_dec_lt(v_i_992_, v___x_995_);
if (v___x_996_ == 0)
{
lean_dec_ref(v_source_993_);
lean_dec(v_i_992_);
return v_target_994_;
}
else
{
lean_object* v_es_997_; lean_object* v___x_998_; lean_object* v_source_999_; lean_object* v_target_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_es_997_ = lean_array_fget(v_source_993_, v_i_992_);
v___x_998_ = lean_box(0);
v_source_999_ = lean_array_fset(v_source_993_, v_i_992_, v___x_998_);
v_target_1000_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_994_, v_es_997_);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_i_992_, v___x_1001_);
lean_dec(v_i_992_);
v_i_992_ = v___x_1002_;
v_source_993_ = v_source_999_;
v_target_994_ = v_target_1000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_nbuckets_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1005_ = lean_array_get_size(v_data_1004_);
v___x_1006_ = lean_unsigned_to_nat(2u);
v_nbuckets_1007_ = lean_nat_mul(v___x_1005_, v___x_1006_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v___x_1009_ = lean_box(0);
v___x_1010_ = lean_mk_array(v_nbuckets_1007_, v___x_1009_);
v___x_1011_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1008_, v_data_1004_, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1012_, lean_object* v_a_1013_, lean_object* v_b_1014_){
_start:
{
lean_object* v_size_1015_; lean_object* v_buckets_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1059_; 
v_size_1015_ = lean_ctor_get(v_m_1012_, 0);
v_buckets_1016_ = lean_ctor_get(v_m_1012_, 1);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_m_1012_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1018_ = v_m_1012_;
v_isShared_1019_ = v_isSharedCheck_1059_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_buckets_1016_);
lean_inc(v_size_1015_);
lean_dec(v_m_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1059_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; uint64_t v___x_1021_; uint64_t v___x_1022_; uint64_t v___x_1023_; uint64_t v_fold_1024_; uint64_t v___x_1025_; uint64_t v___x_1026_; uint64_t v___x_1027_; size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; lean_object* v_bkt_1033_; uint8_t v___x_1034_; 
v___x_1020_ = lean_array_get_size(v_buckets_1016_);
v___x_1021_ = lean_string_hash(v_a_1013_);
v___x_1022_ = 32ULL;
v___x_1023_ = lean_uint64_shift_right(v___x_1021_, v___x_1022_);
v_fold_1024_ = lean_uint64_xor(v___x_1021_, v___x_1023_);
v___x_1025_ = 16ULL;
v___x_1026_ = lean_uint64_shift_right(v_fold_1024_, v___x_1025_);
v___x_1027_ = lean_uint64_xor(v_fold_1024_, v___x_1026_);
v___x_1028_ = lean_uint64_to_usize(v___x_1027_);
v___x_1029_ = lean_usize_of_nat(v___x_1020_);
v___x_1030_ = ((size_t)1ULL);
v___x_1031_ = lean_usize_sub(v___x_1029_, v___x_1030_);
v___x_1032_ = lean_usize_land(v___x_1028_, v___x_1031_);
v_bkt_1033_ = lean_array_uget_borrowed(v_buckets_1016_, v___x_1032_);
v___x_1034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1013_, v_bkt_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v_size_x27_1036_; lean_object* v___x_1037_; lean_object* v_buckets_x27_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1035_ = lean_unsigned_to_nat(1u);
v_size_x27_1036_ = lean_nat_add(v_size_1015_, v___x_1035_);
lean_dec(v_size_1015_);
lean_inc(v_bkt_1033_);
v___x_1037_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1037_, 0, v_a_1013_);
lean_ctor_set(v___x_1037_, 1, v_b_1014_);
lean_ctor_set(v___x_1037_, 2, v_bkt_1033_);
v_buckets_x27_1038_ = lean_array_uset(v_buckets_1016_, v___x_1032_, v___x_1037_);
v___x_1039_ = lean_unsigned_to_nat(4u);
v___x_1040_ = lean_nat_mul(v_size_x27_1036_, v___x_1039_);
v___x_1041_ = lean_unsigned_to_nat(3u);
v___x_1042_ = lean_nat_div(v___x_1040_, v___x_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_array_get_size(v_buckets_x27_1038_);
v___x_1044_ = lean_nat_dec_le(v___x_1042_, v___x_1043_);
lean_dec(v___x_1042_);
if (v___x_1044_ == 0)
{
lean_object* v_val_1045_; lean_object* v___x_1047_; 
v_val_1045_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1038_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_val_1045_);
lean_ctor_set(v___x_1018_, 0, v_size_x27_1036_);
v___x_1047_ = v___x_1018_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_size_x27_1036_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_val_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
else
{
lean_object* v___x_1050_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_buckets_x27_1038_);
lean_ctor_set(v___x_1018_, 0, v_size_x27_1036_);
v___x_1050_ = v___x_1018_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_size_x27_1036_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_buckets_x27_1038_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v___x_1052_; lean_object* v_buckets_x27_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_inc(v_bkt_1033_);
v___x_1052_ = lean_box(0);
v_buckets_x27_1053_ = lean_array_uset(v_buckets_1016_, v___x_1032_, v___x_1052_);
v___x_1054_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1013_, v_b_1014_, v_bkt_1033_);
v___x_1055_ = lean_array_uset(v_buckets_x27_1053_, v___x_1032_, v___x_1054_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v___x_1055_);
v___x_1057_ = v___x_1018_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_size_1015_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1068_, size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_b_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_usize_dec_lt(v_i_1070_, v_sz_1069_);
if (v___x_1072_ == 0)
{
return v_b_1071_;
}
else
{
lean_object* v_fst_1073_; lean_object* v_snd_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1124_; 
v_fst_1073_ = lean_ctor_get(v_b_1071_, 0);
v_snd_1074_ = lean_ctor_get(v_b_1071_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_b_1071_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1076_ = v_b_1071_;
v_isShared_1077_ = v_isSharedCheck_1124_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_snd_1074_);
lean_inc(v_fst_1073_);
lean_dec(v_b_1071_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1124_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v_order_1081_; lean_object* v_fst_1093_; lean_object* v_snd_1094_; lean_object* v_a_1097_; lean_object* v_filePath_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; 
v_a_1097_ = lean_array_uget_borrowed(v_as_1068_, v_i_1070_);
v_filePath_1098_ = lean_ctor_get(v_a_1097_, 0);
lean_inc_ref_n(v_filePath_1098_, 2);
v___f_1099_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1099_, 0, v_filePath_1098_);
v___x_1100_ = l_System_FilePath_extension(v_filePath_1098_);
if (lean_obj_tag(v___x_1100_) == 1)
{
lean_object* v_val_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_val_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_val_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v___x_1102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1103_ = lean_string_dec_eq(v_val_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1105_ = lean_string_dec_eq(v_val_1101_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1107_ = lean_string_dec_eq(v_val_1101_, v___x_1106_);
if (v___x_1107_ == 0)
{
lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1109_ = lean_string_dec_eq(v_val_1101_, v___x_1108_);
lean_dec(v_val_1101_);
if (v___x_1109_ == 0)
{
lean_inc_ref(v_filePath_1098_);
v_fst_1093_ = v_filePath_1098_;
v_snd_1094_ = v___f_1099_;
goto v___jp_1092_;
}
else
{
lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v___f_1099_);
lean_inc_ref_n(v_filePath_1098_, 2);
v___f_1110_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1110_, 0, v_filePath_1098_);
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1112_ = l_System_FilePath_withExtension(v_filePath_1098_, v___x_1111_);
v___x_1113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1114_ = l_System_FilePath_withExtension(v___x_1112_, v___x_1113_);
v_fst_1093_ = v___x_1114_;
v_snd_1094_ = v___f_1110_;
goto v___jp_1092_;
}
}
else
{
lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec(v_val_1101_);
lean_dec_ref(v___f_1099_);
lean_inc_ref_n(v_filePath_1098_, 2);
v___f_1115_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1115_, 0, v_filePath_1098_);
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1117_ = l_System_FilePath_withExtension(v_filePath_1098_, v___x_1116_);
v_fst_1093_ = v___x_1117_;
v_snd_1094_ = v___f_1115_;
goto v___jp_1092_;
}
}
else
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v_val_1101_);
lean_dec_ref(v___f_1099_);
lean_inc_ref_n(v_filePath_1098_, 2);
v___f_1118_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1118_, 0, v_filePath_1098_);
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1120_ = l_System_FilePath_withExtension(v_filePath_1098_, v___x_1119_);
v_fst_1093_ = v___x_1120_;
v_snd_1094_ = v___f_1118_;
goto v___jp_1092_;
}
}
else
{
lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_val_1101_);
lean_dec_ref(v___f_1099_);
lean_inc_ref_n(v_filePath_1098_, 2);
v___f_1121_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1121_, 0, v_filePath_1098_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1123_ = l_System_FilePath_withExtension(v_filePath_1098_, v___x_1122_);
v_fst_1093_ = v___x_1123_;
v_snd_1094_ = v___f_1121_;
goto v___jp_1092_;
}
}
else
{
lean_dec(v___x_1100_);
lean_inc_ref(v_filePath_1098_);
v_fst_1093_ = v_filePath_1098_;
v_snd_1094_ = v___f_1099_;
goto v___jp_1092_;
}
v___jp_1078_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1074_, v___y_1079_, v___x_1082_);
v___x_1084_ = lean_apply_1(v___y_1080_, v___x_1083_);
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1074_, v___y_1079_, v___x_1084_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v___x_1085_);
lean_ctor_set(v___x_1076_, 0, v_order_1081_);
v___x_1087_ = v___x_1076_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_order_1081_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
size_t v___x_1088_; size_t v___x_1089_; 
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1070_, v___x_1088_);
v_i_1070_ = v___x_1089_;
v_b_1071_ = v___x_1087_;
goto _start;
}
}
v___jp_1092_:
{
uint8_t v___x_1095_; 
v___x_1095_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1074_, v_fst_1093_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; 
lean_inc_ref(v_fst_1093_);
v___x_1096_ = lean_array_push(v_fst_1073_, v_fst_1093_);
v___y_1079_ = v_fst_1093_;
v___y_1080_ = v_snd_1094_;
v_order_1081_ = v___x_1096_;
goto v___jp_1078_;
}
else
{
v___y_1079_ = v_fst_1093_;
v___y_1080_ = v_snd_1094_;
v_order_1081_ = v_fst_1073_;
goto v___jp_1078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1125_, lean_object* v_sz_1126_, lean_object* v_i_1127_, lean_object* v_b_1128_){
_start:
{
size_t v_sz_boxed_1129_; size_t v_i_boxed_1130_; lean_object* v_res_1131_; 
v_sz_boxed_1129_ = lean_unbox_usize(v_sz_1126_);
lean_dec(v_sz_1126_);
v_i_boxed_1130_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1125_, v_sz_boxed_1129_, v_i_boxed_1130_, v_b_1128_);
lean_dec_ref(v_as_1125_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1134_ = lean_panic_fn_borrowed(v___x_1133_, v_msg_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1138_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1139_ = lean_unsigned_to_nat(11u);
v___x_1140_ = lean_unsigned_to_nat(163u);
v___x_1141_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1142_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1143_ = l_mkPanicMessageWithDecl(v___x_1142_, v___x_1141_, v___x_1140_, v___x_1139_, v___x_1138_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1144_, lean_object* v_x_1145_){
_start:
{
if (lean_obj_tag(v_x_1145_) == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1147_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1146_);
return v___x_1147_;
}
else
{
lean_object* v_key_1148_; lean_object* v_value_1149_; lean_object* v_tail_1150_; uint8_t v___x_1151_; 
v_key_1148_ = lean_ctor_get(v_x_1145_, 0);
v_value_1149_ = lean_ctor_get(v_x_1145_, 1);
v_tail_1150_ = lean_ctor_get(v_x_1145_, 2);
v___x_1151_ = lean_string_dec_eq(v_key_1148_, v_a_1144_);
if (v___x_1151_ == 0)
{
v_x_1145_ = v_tail_1150_;
goto _start;
}
else
{
lean_inc(v_value_1149_);
return v_value_1149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1153_, v_x_1154_);
lean_dec(v_x_1154_);
lean_dec_ref(v_a_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_buckets_1158_; lean_object* v___x_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; uint64_t v___x_1162_; uint64_t v_fold_1163_; uint64_t v___x_1164_; uint64_t v___x_1165_; uint64_t v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_buckets_1158_ = lean_ctor_get(v_m_1156_, 1);
v___x_1159_ = lean_array_get_size(v_buckets_1158_);
v___x_1160_ = lean_string_hash(v_a_1157_);
v___x_1161_ = 32ULL;
v___x_1162_ = lean_uint64_shift_right(v___x_1160_, v___x_1161_);
v_fold_1163_ = lean_uint64_xor(v___x_1160_, v___x_1162_);
v___x_1164_ = 16ULL;
v___x_1165_ = lean_uint64_shift_right(v_fold_1163_, v___x_1164_);
v___x_1166_ = lean_uint64_xor(v_fold_1163_, v___x_1165_);
v___x_1167_ = lean_uint64_to_usize(v___x_1166_);
v___x_1168_ = lean_usize_of_nat(v___x_1159_);
v___x_1169_ = ((size_t)1ULL);
v___x_1170_ = lean_usize_sub(v___x_1168_, v___x_1169_);
v___x_1171_ = lean_usize_land(v___x_1167_, v___x_1170_);
v___x_1172_ = lean_array_uget_borrowed(v_buckets_1158_, v___x_1171_);
v___x_1173_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1157_, v___x_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1174_, v_a_1175_);
lean_dec_ref(v_a_1175_);
lean_dec_ref(v_m_1174_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1177_, size_t v_sz_1178_, size_t v_i_1179_, lean_object* v_bs_1180_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_lt(v_i_1179_, v_sz_1178_);
if (v___x_1181_ == 0)
{
return v_bs_1180_;
}
else
{
lean_object* v_v_1182_; lean_object* v___x_1183_; lean_object* v_bs_x27_1184_; lean_object* v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
v_v_1182_ = lean_array_uget(v_bs_1180_, v_i_1179_);
v___x_1183_ = lean_unsigned_to_nat(0u);
v_bs_x27_1184_ = lean_array_uset(v_bs_1180_, v_i_1179_, v___x_1183_);
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1177_, v_v_1182_);
lean_dec(v_v_1182_);
v___x_1186_ = ((size_t)1ULL);
v___x_1187_ = lean_usize_add(v_i_1179_, v___x_1186_);
v___x_1188_ = lean_array_uset(v_bs_x27_1184_, v_i_1179_, v___x_1185_);
v_i_1179_ = v___x_1187_;
v_bs_1180_ = v___x_1188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1190_, lean_object* v_sz_1191_, lean_object* v_i_1192_, lean_object* v_bs_1193_){
_start:
{
size_t v_sz_boxed_1194_; size_t v_i_boxed_1195_; lean_object* v_res_1196_; 
v_sz_boxed_1194_ = lean_unbox_usize(v_sz_1191_);
lean_dec(v_sz_1191_);
v_i_boxed_1195_ = lean_unbox_usize(v_i_1192_);
lean_dec(v_i_1192_);
v_res_1196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1190_, v_sz_boxed_1194_, v_i_boxed_1195_, v_bs_1193_);
lean_dec_ref(v___x_1190_);
return v_res_1196_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_box(0);
v___x_1200_ = lean_unsigned_to_nat(16u);
v___x_1201_ = lean_mk_array(v___x_1200_, v___x_1199_);
return v___x_1201_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v_byBase_1204_; 
v___x_1202_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1203_ = lean_unsigned_to_nat(0u);
v_byBase_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1204_, 0, v___x_1203_);
lean_ctor_set(v_byBase_1204_, 1, v___x_1202_);
return v_byBase_1204_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1205_; lean_object* v_order_1206_; lean_object* v___x_1207_; 
v_byBase_1205_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1206_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_order_1206_);
lean_ctor_set(v___x_1207_, 1, v_byBase_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1208_){
_start:
{
lean_object* v___x_1209_; size_t v_sz_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v_fst_1213_; lean_object* v_snd_1214_; size_t v_sz_1215_; lean_object* v___x_1216_; 
v___x_1209_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1210_ = lean_array_size(v_regions_1208_);
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1208_, v_sz_1210_, v___x_1211_, v___x_1209_);
v_fst_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_fst_1213_);
v_snd_1214_ = lean_ctor_get(v___x_1212_, 1);
lean_inc(v_snd_1214_);
lean_dec_ref(v___x_1212_);
v_sz_1215_ = lean_array_size(v_fst_1213_);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1214_, v_sz_1215_, v___x_1211_, v_fst_1213_);
lean_dec(v_snd_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1217_);
lean_dec_ref(v_regions_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1219_, lean_object* v_m_1220_, lean_object* v_a_1221_, lean_object* v_fallback_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1220_, v_a_1221_, v_fallback_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1224_, lean_object* v_m_1225_, lean_object* v_a_1226_, lean_object* v_fallback_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1224_, v_m_1225_, v_a_1226_, v_fallback_1227_);
lean_dec(v_fallback_1227_);
lean_dec_ref(v_a_1226_);
lean_dec_ref(v_m_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1229_, lean_object* v_m_1230_, lean_object* v_a_1231_, lean_object* v_b_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1230_, v_a_1231_, v_b_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1234_, lean_object* v_m_1235_, lean_object* v_a_1236_){
_start:
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1235_, v_a_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1238_, lean_object* v_m_1239_, lean_object* v_a_1240_){
_start:
{
uint8_t v_res_1241_; lean_object* v_r_1242_; 
v_res_1241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1238_, v_m_1239_, v_a_1240_);
lean_dec_ref(v_a_1240_);
lean_dec_ref(v_m_1239_);
v_r_1242_ = lean_box(v_res_1241_);
return v_r_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1243_, lean_object* v_a_1244_, lean_object* v_fallback_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1244_, v_fallback_1245_, v_x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1248_, lean_object* v_a_1249_, lean_object* v_fallback_1250_, lean_object* v_x_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1248_, v_a_1249_, v_fallback_1250_, v_x_1251_);
lean_dec(v_x_1251_);
lean_dec(v_fallback_1250_);
lean_dec_ref(v_a_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1253_, lean_object* v_a_1254_, lean_object* v_x_1255_){
_start:
{
uint8_t v___x_1256_; 
v___x_1256_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1254_, v_x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1257_, lean_object* v_a_1258_, lean_object* v_x_1259_){
_start:
{
uint8_t v_res_1260_; lean_object* v_r_1261_; 
v_res_1260_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1257_, v_a_1258_, v_x_1259_);
lean_dec(v_x_1259_);
lean_dec_ref(v_a_1258_);
v_r_1261_ = lean_box(v_res_1260_);
return v_r_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1262_, lean_object* v_data_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1265_, lean_object* v_a_1266_, lean_object* v_b_1267_, lean_object* v_x_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1266_, v_b_1267_, v_x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1270_, lean_object* v_i_1271_, lean_object* v_source_1272_, lean_object* v_target_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1271_, v_source_1272_, v_target_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1275_, lean_object* v_x_1276_, lean_object* v_x_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1276_, v_x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1279_, size_t v_sz_1280_, size_t v_i_1281_, lean_object* v_b_1282_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_lt(v_i_1281_, v_sz_1280_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_b_1282_);
return v___x_1285_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1287_; 
v_a_1286_ = lean_array_uget_borrowed(v_as_1279_, v_i_1281_);
v___x_1287_ = lean_compacted_region_read(v_a_1286_, v_b_1282_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_snd_1289_; lean_object* v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_snd_1289_ = lean_ctor_get(v_a_1288_, 1);
lean_inc(v_snd_1289_);
lean_dec(v_a_1288_);
v___x_1290_ = lean_array_push(v_b_1282_, v_snd_1289_);
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_add(v_i_1281_, v___x_1291_);
v_i_1281_ = v___x_1292_;
v_b_1282_ = v___x_1290_;
goto _start;
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_b_1282_);
v_a_1294_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1287_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1287_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1302_, lean_object* v_sz_1303_, lean_object* v_i_1304_, lean_object* v_b_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1303_);
lean_dec(v_sz_1303_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1302_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1305_);
lean_dec_ref(v_as_1302_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1312_){
_start:
{
lean_object* v_oleanRegions_1314_; lean_object* v___x_1315_; size_t v_sz_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v_oleanRegions_1314_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1312_);
v___x_1315_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1312_);
v_sz_1316_ = lean_array_size(v___x_1315_);
v___x_1317_ = ((size_t)0ULL);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1315_, v_sz_1316_, v___x_1317_, v_oleanRegions_1314_);
lean_dec_ref(v___x_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; size_t v_sz_1321_; lean_object* v___x_1322_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = l_Lean_ModuleArtifacts_irParts(v_arts_1312_);
v_sz_1321_ = lean_array_size(v___x_1320_);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1320_, v_sz_1321_, v___x_1317_, v_oleanRegions_1314_);
lean_dec_ref(v___x_1320_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = l_Array_append___redArg(v_a_1319_, v_a_1323_);
lean_dec(v_a_1323_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
lean_dec(v_a_1319_);
return v___x_1322_;
}
}
else
{
lean_dec_ref(v_arts_1312_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1335_){
_start:
{
if (lean_obj_tag(v_e_1335_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1346_; 
v_a_1337_ = lean_ctor_get(v_e_1335_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_e_1335_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1339_ = v_e_1335_;
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v_e_1335_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1346_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1344_; 
v___x_1341_ = lean_io_error_to_string(v_a_1337_);
v___x_1342_ = lean_mk_io_user_error(v___x_1341_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set_tag(v___x_1339_, 1);
lean_ctor_set(v___x_1339_, 0, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
v_a_1347_ = lean_ctor_get(v_e_1335_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_e_1335_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v_e_1335_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v_e_1335_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set_tag(v___x_1349_, 0);
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1358_, lean_object* v_e_1359_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1362_, lean_object* v_e_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1362_, v_e_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1366_, lean_object* v___y_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_fst_1370_; lean_object* v_snd_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1399_; 
v_fst_1370_ = lean_ctor_get(v_a_1368_, 0);
v_snd_1371_ = lean_ctor_get(v_a_1368_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_a_1368_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1373_ = v_a_1368_;
v_isShared_1374_ = v_isSharedCheck_1399_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_snd_1371_);
lean_inc(v_fst_1370_);
lean_dec(v_a_1368_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1399_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = lean_array_get_size(v_a_1366_);
v___x_1376_ = lean_nat_dec_lt(v_snd_1371_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1378_; 
if (v_isShared_1374_ == 0)
{
v___x_1378_ = v___x_1373_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_fst_1370_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_snd_1371_);
v___x_1378_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1382_ = lean_array_get_borrowed(v___x_1381_, v_a_1366_, v_snd_1371_);
lean_inc(v___x_1382_);
v___x_1383_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1382_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = l_Array_append___redArg(v_fst_1370_, v_a_1384_);
lean_dec(v_a_1384_);
v___x_1386_ = lean_nat_add(v_snd_1371_, v___y_1367_);
lean_dec(v_snd_1371_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___x_1386_);
lean_ctor_set(v___x_1373_, 0, v___x_1385_);
v___x_1388_ = v___x_1373_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
v_a_1368_ = v___x_1388_;
goto _start;
}
}
else
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1398_; 
lean_del_object(v___x_1373_);
lean_dec(v_snd_1371_);
lean_dec(v_fst_1370_);
v_a_1391_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1393_ = v___x_1383_;
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1383_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1398_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1396_; 
if (v_isShared_1394_ == 0)
{
v___x_1396_ = v___x_1393_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_a_1391_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1400_, lean_object* v___y_1401_, lean_object* v_a_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1400_, v___y_1401_, v_a_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v_a_1400_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1405_, lean_object* v___y_1406_, lean_object* v___x_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1405_, v___y_1406_, v___x_1407_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1418_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1418_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_fst_1414_; lean_object* v___x_1416_; 
v_fst_1414_ = lean_ctor_get(v_a_1410_, 0);
lean_inc(v_fst_1414_);
lean_dec(v_a_1410_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 1);
lean_ctor_set(v___x_1412_, 0, v_fst_1414_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_fst_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
v_a_1419_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1409_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1409_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
lean_ctor_set_tag(v___x_1421_, 0);
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1427_, lean_object* v___y_1428_, lean_object* v___x_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1427_, v___y_1428_, v___x_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v_a_1427_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1432_, lean_object* v_a_1433_, lean_object* v___y_1434_, lean_object* v_a_1435_, lean_object* v_b_1436_){
_start:
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_lt(v_a_1435_, v_upperBound_1432_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; 
lean_dec(v_a_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v_a_1433_);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_b_1436_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1435_);
v___x_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v_a_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v_a_1433_);
v___f_1443_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1443_, 0, v_a_1433_);
lean_closure_set(v___f_1443_, 1, v___y_1434_);
lean_closure_set(v___f_1443_, 2, v___x_1442_);
v___x_1444_ = lean_io_as_task(v___f_1443_, v___x_1440_);
v___x_1445_ = lean_array_push(v_b_1436_, v___x_1444_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_a_1435_, v___x_1446_);
lean_dec(v_a_1435_);
v_a_1435_ = v___x_1447_;
v_b_1436_ = v___x_1445_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1449_, lean_object* v_a_1450_, lean_object* v___y_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1449_, v_a_1450_, v___y_1451_, v_a_1452_, v_b_1453_);
lean_dec(v_upperBound_1449_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1456_, size_t v_sz_1457_, size_t v_i_1458_, lean_object* v_b_1459_){
_start:
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_usize_dec_lt(v_i_1458_, v_sz_1457_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_b_1459_);
return v___x_1462_;
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v_a_1463_ = lean_array_uget_borrowed(v_as_1456_, v_i_1458_);
lean_inc(v_a_1463_);
v___x_1464_ = lean_task_get_own(v_a_1463_);
v___x_1465_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1464_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; size_t v___x_1468_; size_t v___x_1469_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = l_Array_append___redArg(v_b_1459_, v_a_1466_);
lean_dec(v_a_1466_);
v___x_1468_ = ((size_t)1ULL);
v___x_1469_ = lean_usize_add(v_i_1458_, v___x_1468_);
v_i_1458_ = v___x_1469_;
v_b_1459_ = v___x_1467_;
goto _start;
}
else
{
lean_dec_ref(v_b_1459_);
return v___x_1465_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1471_, lean_object* v_sz_1472_, lean_object* v_i_1473_, lean_object* v_b_1474_, lean_object* v___y_1475_){
_start:
{
size_t v_sz_boxed_1476_; size_t v_i_boxed_1477_; lean_object* v_res_1478_; 
v_sz_boxed_1476_ = lean_unbox_usize(v_sz_1472_);
lean_dec(v_sz_1472_);
v_i_boxed_1477_ = lean_unbox_usize(v_i_1473_);
lean_dec(v_i_1473_);
v_res_1478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1471_, v_sz_boxed_1476_, v_i_boxed_1477_, v_b_1474_);
lean_dec_ref(v_as_1471_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1479_, size_t v_i_1480_, lean_object* v_bs_1481_){
_start:
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_usize_dec_lt(v_i_1480_, v_sz_1479_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_bs_1481_);
return v___x_1483_;
}
else
{
lean_object* v_v_1484_; lean_object* v___x_1485_; 
v_v_1484_ = lean_array_uget_borrowed(v_bs_1481_, v_i_1480_);
lean_inc(v_v_1484_);
v___x_1485_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1484_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_bs_1481_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v_bs_x27_1496_; size_t v___x_1497_; size_t v___x_1498_; lean_object* v___x_1499_; 
v_a_1494_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1485_, 1);
v___x_1495_ = lean_unsigned_to_nat(0u);
v_bs_x27_1496_ = lean_array_uset(v_bs_1481_, v_i_1480_, v___x_1495_);
v___x_1497_ = ((size_t)1ULL);
v___x_1498_ = lean_usize_add(v_i_1480_, v___x_1497_);
v___x_1499_ = lean_array_uset(v_bs_x27_1496_, v_i_1480_, v_a_1494_);
v_i_1480_ = v___x_1498_;
v_bs_1481_ = v___x_1499_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1501_, lean_object* v_i_1502_, lean_object* v_bs_1503_){
_start:
{
size_t v_sz_boxed_1504_; size_t v_i_boxed_1505_; lean_object* v_res_1506_; 
v_sz_boxed_1504_ = lean_unbox_usize(v_sz_1501_);
lean_dec(v_sz_1501_);
v_i_boxed_1505_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_res_1506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1504_, v_i_boxed_1505_, v_bs_1503_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1509_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 4)
{
lean_object* v_elems_1510_; size_t v_sz_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v_elems_1510_ = lean_ctor_get(v_x_1509_, 0);
lean_inc_ref(v_elems_1510_);
lean_dec_ref_known(v_x_1509_, 1);
v_sz_1511_ = lean_array_size(v_elems_1510_);
v___x_1512_ = ((size_t)0ULL);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1511_, v___x_1512_, v_elems_1510_);
return v___x_1513_;
}
else
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1514_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1515_ = lean_unsigned_to_nat(80u);
v___x_1516_ = l_Lean_Json_pretty(v_x_1509_, v___x_1515_);
v___x_1517_ = lean_string_append(v___x_1514_, v___x_1516_);
lean_dec_ref(v___x_1516_);
v___x_1518_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1524_; uint32_t v___x_1525_; 
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_internal_get_hardware_concurrency(v___x_1524_);
return v___x_1525_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1527_ = lean_uint32_to_nat(v___x_1526_);
return v___x_1527_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = lean_unsigned_to_nat(4u);
v___x_1530_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1531_ = lean_nat_dec_le(v___x_1530_, v___x_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v_depsFile_1535_; lean_object* v___x_1536_; 
v___x_1534_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1532_);
v_depsFile_1535_ = l_System_FilePath_addExtension(v_fname_1532_, v___x_1534_);
v___x_1536_ = l_IO_FS_readFile(v_depsFile_1535_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1623_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1623_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1623_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_a_1542_; lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Json_parse(v_a_1537_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; 
lean_dec_ref(v_fname_1532_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v_a_1542_ = v_a_1553_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1555_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1554_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; 
lean_dec_ref(v_fname_1532_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v_a_1542_ = v_a_1556_;
goto v___jp_1541_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___y_1561_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1612_; uint8_t v___x_1622_; 
lean_del_object(v___x_1539_);
lean_dec_ref(v_depsFile_1535_);
v_a_1557_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1558_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1559_ = lean_unsigned_to_nat(4u);
v___x_1622_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1622_ == 0)
{
v___y_1612_ = v___x_1559_;
goto v___jp_1611_;
}
else
{
v___y_1612_ = v___x_1558_;
goto v___jp_1611_;
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_mk_empty_array_with_capacity(v___y_1561_);
v___x_1563_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1557_);
lean_inc(v___y_1561_);
v___x_1564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1561_, v_a_1557_, v___y_1561_, v___x_1563_, v___x_1562_);
lean_dec(v___y_1561_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = lean_array_get_size(v_a_1557_);
lean_dec(v_a_1557_);
v___x_1567_ = lean_nat_mul(v___x_1566_, v___x_1559_);
v___x_1568_ = lean_mk_empty_array_with_capacity(v___x_1567_);
lean_dec(v___x_1567_);
v_sz_1569_ = lean_array_size(v_a_1565_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1565_, v_sz_1569_, v___x_1570_, v___x_1568_);
lean_dec(v_a_1565_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1573_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1573_ = lean_compacted_region_read(v_fname_1532_, v_a_1572_);
lean_dec(v_a_1572_);
lean_dec_ref(v_fname_1532_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_fst_1578_; lean_object* v___x_1580_; 
v_fst_1578_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_fst_1578_);
lean_dec(v_a_1574_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v_fst_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_fst_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
v_a_1583_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1573_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1573_);
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
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
lean_dec_ref(v_fname_1532_);
v_a_1591_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1571_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1571_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_a_1557_);
lean_dec_ref(v_fname_1532_);
v_a_1599_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1564_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1564_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
v___jp_1607_:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_nat_dec_le(v___y_1608_, v___y_1609_);
if (v___x_1610_ == 0)
{
lean_dec(v___y_1609_);
v___y_1561_ = v___y_1608_;
goto v___jp_1560_;
}
else
{
lean_dec(v___y_1608_);
v___y_1561_ = v___y_1609_;
goto v___jp_1560_;
}
}
v___jp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1614_ = lean_io_getenv(v___x_1613_);
v___x_1615_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1614_) == 0)
{
v___y_1608_ = v___x_1615_;
v___y_1609_ = v___y_1612_;
goto v___jp_1607_;
}
else
{
lean_object* v_val_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_val_1616_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v___x_1614_, 1);
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = lean_string_utf8_byte_size(v_val_1616_);
v___x_1619_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1619_, 0, v_val_1616_);
lean_ctor_set(v___x_1619_, 1, v___x_1617_);
lean_ctor_set(v___x_1619_, 2, v___x_1618_);
v___x_1620_ = l_String_Slice_toNat_x3f(v___x_1619_);
lean_dec_ref_known(v___x_1619_, 3);
if (lean_obj_tag(v___x_1620_) == 0)
{
v___y_1608_ = v___x_1615_;
v___y_1609_ = v___y_1612_;
goto v___jp_1607_;
}
else
{
lean_object* v_val_1621_; 
lean_dec(v___y_1612_);
v_val_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_val_1621_);
lean_dec_ref_known(v___x_1620_, 1);
v___y_1608_ = v___x_1615_;
v___y_1609_ = v_val_1621_;
goto v___jp_1607_;
}
}
}
}
}
v___jp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1544_ = lean_string_append(v___x_1543_, v_depsFile_1535_);
lean_dec_ref(v_depsFile_1535_);
v___x_1545_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1546_ = lean_string_append(v___x_1544_, v___x_1545_);
v___x_1547_ = lean_string_append(v___x_1546_, v_a_1542_);
lean_dec_ref(v_a_1542_);
v___x_1548_ = lean_mk_io_user_error(v___x_1547_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1548_);
v___x_1550_ = v___x_1539_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_depsFile_1535_);
lean_dec_ref(v_fname_1532_);
v_a_1624_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1536_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1536_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1635_, lean_object* v___y_1636_, lean_object* v_inst_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1635_, v___y_1636_, v_a_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1641_, lean_object* v___y_1642_, lean_object* v_inst_1643_, lean_object* v_a_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1641_, v___y_1642_, v_inst_1643_, v_a_1644_);
lean_dec(v___y_1642_);
lean_dec_ref(v_a_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1647_, lean_object* v_a_1648_, lean_object* v___y_1649_, lean_object* v_inst_1650_, lean_object* v_R_1651_, lean_object* v_a_1652_, lean_object* v_b_1653_, lean_object* v_c_1654_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1647_, v_a_1648_, v___y_1649_, v_a_1652_, v_b_1653_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1657_, lean_object* v_a_1658_, lean_object* v___y_1659_, lean_object* v_inst_1660_, lean_object* v_R_1661_, lean_object* v_a_1662_, lean_object* v_b_1663_, lean_object* v_c_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1657_, v_a_1658_, v___y_1659_, v_inst_1660_, v_R_1661_, v_a_1662_, v_b_1663_, v_c_1664_);
lean_dec(v_upperBound_1657_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1667_, size_t v_sz_1668_, size_t v_i_1669_, lean_object* v_b_1670_){
_start:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_usize_dec_lt(v_i_1669_, v_sz_1668_);
if (v___x_1672_ == 0)
{
return v_b_1670_;
}
else
{
lean_object* v_a_1673_; lean_object* v_cancelTk_x3f_1674_; lean_object* v___x_1675_; 
v_a_1673_ = lean_array_uget_borrowed(v_as_1667_, v_i_1669_);
v_cancelTk_x3f_1674_ = lean_ctor_get(v_a_1673_, 2);
v___x_1675_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1674_) == 1)
{
lean_object* v_val_1682_; lean_object* v___x_1683_; 
v_val_1682_ = lean_ctor_get(v_cancelTk_x3f_1674_, 0);
v___x_1683_ = l_IO_CancelToken_set(v_val_1682_);
goto v___jp_1676_;
}
else
{
goto v___jp_1676_;
}
v___jp_1676_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; size_t v___x_1679_; size_t v___x_1680_; 
lean_inc(v_a_1673_);
v___x_1677_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1673_);
v___x_1678_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1677_);
lean_dec(v___x_1677_);
v___x_1679_ = ((size_t)1ULL);
v___x_1680_ = lean_usize_add(v_i_1669_, v___x_1679_);
v_i_1669_ = v___x_1680_;
v_b_1670_ = v___x_1675_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1684_){
_start:
{
lean_object* v_children_1686_; lean_object* v___x_1687_; size_t v_sz_1688_; size_t v___x_1689_; lean_object* v___x_1690_; 
v_children_1686_ = lean_ctor_get(v_s_1684_, 1);
v___x_1687_ = lean_box(0);
v_sz_1688_ = lean_array_size(v_children_1686_);
v___x_1689_ = ((size_t)0ULL);
v___x_1690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1686_, v_sz_1688_, v___x_1689_, v___x_1687_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1691_, lean_object* v_a_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1691_);
lean_dec_ref(v_s_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1694_, lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_b_1697_, lean_object* v___y_1698_){
_start:
{
size_t v_sz_boxed_1699_; size_t v_i_boxed_1700_; lean_object* v_res_1701_; 
v_sz_boxed_1699_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1700_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1694_, v_sz_boxed_1699_, v_i_boxed_1700_, v_b_1697_);
lean_dec_ref(v_as_1694_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1702_, lean_object* v_m_1703_){
_start:
{
lean_object* v_result_x3f_1704_; 
v_result_x3f_1704_ = lean_ctor_get(v_snap_1702_, 4);
lean_inc(v_result_x3f_1704_);
if (lean_obj_tag(v_result_x3f_1704_) == 1)
{
lean_object* v_val_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1804_; 
v_val_1705_ = lean_ctor_get(v_result_x3f_1704_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_result_x3f_1704_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1707_ = v_result_x3f_1704_;
v_isShared_1708_ = v_isSharedCheck_1804_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_val_1705_);
lean_dec(v_result_x3f_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1804_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_toSnapshot_1709_; lean_object* v_metaSnap_1710_; lean_object* v_ictx_1711_; lean_object* v_stx_1712_; lean_object* v_parserState_1713_; lean_object* v_processedSnap_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1803_; 
v_toSnapshot_1709_ = lean_ctor_get(v_snap_1702_, 0);
v_metaSnap_1710_ = lean_ctor_get(v_snap_1702_, 1);
v_ictx_1711_ = lean_ctor_get(v_snap_1702_, 2);
v_stx_1712_ = lean_ctor_get(v_snap_1702_, 3);
v_parserState_1713_ = lean_ctor_get(v_val_1705_, 0);
v_processedSnap_1714_ = lean_ctor_get(v_val_1705_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_val_1705_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1716_ = v_val_1705_;
v_isShared_1717_ = v_isSharedCheck_1803_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_processedSnap_1714_);
lean_inc(v_parserState_1713_);
lean_dec(v_val_1705_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1803_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v_processed_1718_; lean_object* v_result_x3f_1719_; 
v_processed_1718_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1714_);
v_result_x3f_1719_ = lean_ctor_get(v_processed_1718_, 2);
lean_inc(v_result_x3f_1719_);
if (lean_obj_tag(v_result_x3f_1719_) == 1)
{
lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1802_; 
v_val_1720_ = lean_ctor_get(v_result_x3f_1719_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_result_x3f_1719_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1722_ = v_result_x3f_1719_;
v_isShared_1723_ = v_isSharedCheck_1802_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_dec(v_result_x3f_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1802_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_cmdState_1724_; lean_object* v_toSnapshot_1725_; lean_object* v_metaSnap_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1800_; 
v_cmdState_1724_ = lean_ctor_get(v_val_1720_, 0);
lean_inc_ref(v_cmdState_1724_);
v_toSnapshot_1725_ = lean_ctor_get(v_processed_1718_, 0);
v_metaSnap_1726_ = lean_ctor_get(v_processed_1718_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_processed_1718_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_processed_1718_, 2);
lean_dec(v_unused_1801_);
v___x_1728_ = v_processed_1718_;
v_isShared_1729_ = v_isSharedCheck_1800_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_metaSnap_1726_);
lean_inc(v_toSnapshot_1725_);
lean_dec(v_processed_1718_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1800_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_firstCmdSnap_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1798_; 
v_firstCmdSnap_1730_ = lean_ctor_get(v_val_1720_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_val_1720_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_val_1720_, 0);
lean_dec(v_unused_1799_);
v___x_1732_ = v_val_1720_;
v_isShared_1733_ = v_isSharedCheck_1798_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_firstCmdSnap_1730_);
lean_dec(v_val_1720_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1798_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_env_1734_; lean_object* v_messages_1735_; lean_object* v_scopes_1736_; lean_object* v_usedQuotCtxts_1737_; lean_object* v_nextMacroScope_1738_; lean_object* v_maxRecDepth_1739_; lean_object* v_ngen_1740_; lean_object* v_auxDeclNGen_1741_; lean_object* v_infoState_1742_; lean_object* v_traceState_1743_; lean_object* v_snapshotTasks_1744_; lean_object* v_prevLinterStates_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1797_; 
v_env_1734_ = lean_ctor_get(v_cmdState_1724_, 0);
v_messages_1735_ = lean_ctor_get(v_cmdState_1724_, 1);
v_scopes_1736_ = lean_ctor_get(v_cmdState_1724_, 2);
v_usedQuotCtxts_1737_ = lean_ctor_get(v_cmdState_1724_, 3);
v_nextMacroScope_1738_ = lean_ctor_get(v_cmdState_1724_, 4);
v_maxRecDepth_1739_ = lean_ctor_get(v_cmdState_1724_, 5);
v_ngen_1740_ = lean_ctor_get(v_cmdState_1724_, 6);
v_auxDeclNGen_1741_ = lean_ctor_get(v_cmdState_1724_, 7);
v_infoState_1742_ = lean_ctor_get(v_cmdState_1724_, 8);
v_traceState_1743_ = lean_ctor_get(v_cmdState_1724_, 9);
v_snapshotTasks_1744_ = lean_ctor_get(v_cmdState_1724_, 10);
v_prevLinterStates_1745_ = lean_ctor_get(v_cmdState_1724_, 11);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_cmdState_1724_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1747_ = v_cmdState_1724_;
v_isShared_1748_ = v_isSharedCheck_1797_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_prevLinterStates_1745_);
lean_inc(v_snapshotTasks_1744_);
lean_inc(v_traceState_1743_);
lean_inc(v_infoState_1742_);
lean_inc(v_auxDeclNGen_1741_);
lean_inc(v_ngen_1740_);
lean_inc(v_maxRecDepth_1739_);
lean_inc(v_nextMacroScope_1738_);
lean_inc(v_usedQuotCtxts_1737_);
lean_inc(v_scopes_1736_);
lean_inc(v_messages_1735_);
lean_inc(v_env_1734_);
lean_dec(v_cmdState_1724_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1797_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v_mainModule_1750_; uint8_t v___x_1751_; 
v___x_1749_ = l_Lean_Environment_header(v_env_1734_);
v_mainModule_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_mainModule_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_name_eq(v_mainModule_1750_, v_m_1703_);
lean_dec(v_mainModule_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1791_; 
lean_inc(v_stx_1712_);
lean_inc_ref(v_ictx_1711_);
lean_inc_ref(v_metaSnap_1710_);
lean_inc_ref(v_toSnapshot_1709_);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_snap_1702_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; lean_object* v_unused_1793_; lean_object* v_unused_1794_; lean_object* v_unused_1795_; lean_object* v_unused_1796_; 
v_unused_1792_ = lean_ctor_get(v_snap_1702_, 4);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_snap_1702_, 3);
lean_dec(v_unused_1793_);
v_unused_1794_ = lean_ctor_get(v_snap_1702_, 2);
lean_dec(v_unused_1794_);
v_unused_1795_ = lean_ctor_get(v_snap_1702_, 1);
lean_dec(v_unused_1795_);
v_unused_1796_ = lean_ctor_get(v_snap_1702_, 0);
lean_dec(v_unused_1796_);
v___x_1753_ = v_snap_1702_;
v_isShared_1754_ = v_isSharedCheck_1791_;
goto v_resetjp_1752_;
}
else
{
lean_dec(v_snap_1702_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1791_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_idx_1755_; lean_object* v_parentIdxs_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1789_; 
v_idx_1755_ = lean_ctor_get(v_auxDeclNGen_1741_, 1);
v_parentIdxs_1756_ = lean_ctor_get(v_auxDeclNGen_1741_, 2);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_auxDeclNGen_1741_);
if (v_isSharedCheck_1789_ == 0)
{
lean_object* v_unused_1790_; 
v_unused_1790_ = lean_ctor_get(v_auxDeclNGen_1741_, 0);
lean_dec(v_unused_1790_);
v___x_1758_ = v_auxDeclNGen_1741_;
v_isShared_1759_ = v_isSharedCheck_1789_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_parentIdxs_1756_);
lean_inc(v_idx_1755_);
lean_dec(v_auxDeclNGen_1741_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1789_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_newEnv_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v_newEnv_1760_ = l_Lean_Environment_setMainModule(v_env_1734_, v_m_1703_);
v___x_1761_ = lean_box(0);
v___x_1762_ = l_Lean_mkPrivateName(v_newEnv_1760_, v___x_1761_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1762_);
v___x_1764_ = v___x_1758_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_idx_1755_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_parentIdxs_1756_);
v___x_1764_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v_newCmdState_1766_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 7, v___x_1764_);
lean_ctor_set(v___x_1747_, 0, v_newEnv_1760_);
v_newCmdState_1766_ = v___x_1747_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_newEnv_1760_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_messages_1735_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_scopes_1736_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_usedQuotCtxts_1737_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v_nextMacroScope_1738_);
lean_ctor_set(v_reuseFailAlloc_1787_, 5, v_maxRecDepth_1739_);
lean_ctor_set(v_reuseFailAlloc_1787_, 6, v_ngen_1740_);
lean_ctor_set(v_reuseFailAlloc_1787_, 7, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1787_, 8, v_infoState_1742_);
lean_ctor_set(v_reuseFailAlloc_1787_, 9, v_traceState_1743_);
lean_ctor_set(v_reuseFailAlloc_1787_, 10, v_snapshotTasks_1744_);
lean_ctor_set(v_reuseFailAlloc_1787_, 11, v_prevLinterStates_1745_);
v_newCmdState_1766_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v___x_1768_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v_newCmdState_1766_);
v___x_1768_ = v___x_1732_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_newCmdState_1766_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_firstCmdSnap_1730_);
v___x_1768_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1768_);
v___x_1770_ = v___x_1722_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v_newProcessed_1772_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 2, v___x_1770_);
v_newProcessed_1772_ = v___x_1728_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_toSnapshot_1725_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_metaSnap_1726_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v___x_1770_);
v_newProcessed_1772_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = lean_box(0);
v___x_1774_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1773_, v_newProcessed_1772_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v___x_1774_);
v___x_1776_ = v___x_1716_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_parserState_1713_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1778_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1776_);
v___x_1778_ = v___x_1707_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
lean_object* v___x_1780_; 
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 4, v___x_1778_);
v___x_1780_ = v___x_1753_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_toSnapshot_1709_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_metaSnap_1710_);
lean_ctor_set(v_reuseFailAlloc_1781_, 2, v_ictx_1711_);
lean_ctor_set(v_reuseFailAlloc_1781_, 3, v_stx_1712_);
lean_ctor_set(v_reuseFailAlloc_1781_, 4, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
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
lean_del_object(v___x_1747_);
lean_dec(v_prevLinterStates_1745_);
lean_dec_ref(v_snapshotTasks_1744_);
lean_dec_ref(v_traceState_1743_);
lean_dec_ref(v_infoState_1742_);
lean_dec_ref(v_auxDeclNGen_1741_);
lean_dec_ref(v_ngen_1740_);
lean_dec(v_maxRecDepth_1739_);
lean_dec(v_nextMacroScope_1738_);
lean_dec(v_usedQuotCtxts_1737_);
lean_dec(v_scopes_1736_);
lean_dec_ref(v_messages_1735_);
lean_dec_ref(v_env_1734_);
lean_del_object(v___x_1732_);
lean_dec_ref(v_firstCmdSnap_1730_);
lean_del_object(v___x_1728_);
lean_dec_ref(v_metaSnap_1726_);
lean_dec_ref(v_toSnapshot_1725_);
lean_del_object(v___x_1722_);
lean_del_object(v___x_1716_);
lean_dec_ref(v_parserState_1713_);
lean_del_object(v___x_1707_);
lean_dec(v_m_1703_);
return v_snap_1702_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1719_);
lean_dec(v_processed_1718_);
lean_del_object(v___x_1716_);
lean_dec_ref(v_parserState_1713_);
lean_del_object(v___x_1707_);
lean_dec(v_m_1703_);
return v_snap_1702_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1704_);
lean_dec(v_m_1703_);
return v_snap_1702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1811_, lean_object* v_incr_1812_, lean_object* v_res_1813_){
_start:
{
lean_object* v_cmdState_1815_; lean_object* v_env_1816_; lean_object* v_initModIdxs_1817_; lean_object* v___x_1818_; 
v_cmdState_1815_ = lean_ctor_get(v_res_1813_, 0);
lean_inc_ref(v_cmdState_1815_);
lean_dec_ref(v_res_1813_);
v_env_1816_ = lean_ctor_get(v_cmdState_1815_, 0);
lean_inc_ref(v_env_1816_);
lean_dec_ref(v_cmdState_1815_);
v_initModIdxs_1817_ = lean_ctor_get(v_incr_1812_, 1);
v___x_1818_ = l_Lean_runInitAttrsForModules(v_env_1816_, v_initModIdxs_1817_, v_opts_1811_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1819_, lean_object* v_incr_1820_, lean_object* v_res_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1819_, v_incr_1820_, v_res_1821_);
lean_dec_ref(v_incr_1820_);
lean_dec_ref(v_opts_1819_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_enable_initializer_execution();
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1831_, lean_object* v_incrFile_1832_, lean_object* v_toSave_1833_){
_start:
{
lean_object* v___x_1835_; lean_object* v_regions_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1835_ = l_Lean_Environment_header(v_env_1831_);
v_regions_1836_ = lean_ctor_get(v___x_1835_, 2);
lean_inc_ref(v_regions_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1838_ = lean_box(0);
v___x_1839_ = 1;
v___x_1840_ = lean_compacted_region_save(v_incrFile_1832_, v___x_1837_, v_toSave_1833_, v_regions_1836_, v___x_1838_, v___x_1839_);
lean_dec_ref(v_regions_1836_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1841_, lean_object* v_incrFile_1842_, lean_object* v_toSave_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1841_, v_incrFile_1842_, v_toSave_1843_);
lean_dec_ref(v_toSave_1843_);
lean_dec_ref(v_incrFile_1842_);
lean_dec_ref(v_env_1841_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1846_, lean_object* v_opt_1847_){
_start:
{
lean_object* v_name_1848_; lean_object* v_map_1849_; lean_object* v___x_1850_; 
v_name_1848_ = lean_ctor_get(v_opt_1847_, 0);
v_map_1849_ = lean_ctor_get(v_opts_1846_, 0);
v___x_1850_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1849_, v_name_1848_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_box(0);
return v___x_1851_;
}
else
{
lean_object* v_val_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1861_; 
v_val_1852_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1854_ = v___x_1850_;
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_val_1852_);
lean_dec(v___x_1850_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
if (lean_obj_tag(v_val_1852_) == 0)
{
lean_object* v_v_1856_; lean_object* v___x_1858_; 
v_v_1856_ = lean_ctor_get(v_val_1852_, 0);
lean_inc_ref(v_v_1856_);
lean_dec_ref_known(v_val_1852_, 1);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v_v_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_v_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
else
{
lean_object* v___x_1860_; 
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
v___x_1860_ = lean_box(0);
return v___x_1860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1862_, lean_object* v_opt_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1862_, v_opt_1863_);
lean_dec_ref(v_opt_1863_);
lean_dec_ref(v_opts_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1865_, lean_object* v_opt_1866_){
_start:
{
lean_object* v_name_1867_; lean_object* v_defValue_1868_; lean_object* v_map_1869_; lean_object* v___x_1870_; 
v_name_1867_ = lean_ctor_get(v_opt_1866_, 0);
v_defValue_1868_ = lean_ctor_get(v_opt_1866_, 1);
v_map_1869_ = lean_ctor_get(v_opts_1865_, 0);
v___x_1870_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1869_, v_name_1867_);
if (lean_obj_tag(v___x_1870_) == 0)
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_unbox(v_defValue_1868_);
return v___x_1871_;
}
else
{
lean_object* v_val_1872_; 
v_val_1872_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v___x_1870_, 1);
if (lean_obj_tag(v_val_1872_) == 1)
{
uint8_t v_v_1873_; 
v_v_1873_ = lean_ctor_get_uint8(v_val_1872_, 0);
lean_dec_ref_known(v_val_1872_, 0);
return v_v_1873_;
}
else
{
uint8_t v___x_1874_; 
lean_dec(v_val_1872_);
v___x_1874_ = lean_unbox(v_defValue_1868_);
return v___x_1874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1875_, lean_object* v_opt_1876_){
_start:
{
uint8_t v_res_1877_; lean_object* v_r_1878_; 
v_res_1877_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1875_, v_opt_1876_);
lean_dec_ref(v_opt_1876_);
lean_dec_ref(v_opts_1875_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_hOpt_1881_){
_start:
{
lean_inc_ref(v_hOpt_1881_);
return v_hOpt_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_hOpt_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_Elab_runFrontend___lam__0(v_x_1882_, v_x_1883_, v_hOpt_1884_);
lean_dec_ref(v_hOpt_1884_);
lean_dec_ref(v_x_1883_);
lean_dec(v_x_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(size_t v_sz_1886_, size_t v_i_1887_, lean_object* v_bs_1888_){
_start:
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_usize_dec_lt(v_i_1887_, v_sz_1886_);
if (v___x_1889_ == 0)
{
return v_bs_1888_;
}
else
{
lean_object* v_v_1890_; lean_object* v___x_1891_; lean_object* v_bs_x27_1892_; lean_object* v___x_1893_; size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
v_v_1890_ = lean_array_uget(v_bs_1888_, v_i_1887_);
v___x_1891_ = lean_unsigned_to_nat(0u);
v_bs_x27_1892_ = lean_array_uset(v_bs_1888_, v_i_1887_, v___x_1891_);
v___x_1893_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1890_);
v___x_1894_ = ((size_t)1ULL);
v___x_1895_ = lean_usize_add(v_i_1887_, v___x_1894_);
v___x_1896_ = lean_array_uset(v_bs_x27_1892_, v_i_1887_, v___x_1893_);
v_i_1887_ = v___x_1895_;
v_bs_1888_ = v___x_1896_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6___boxed(lean_object* v_sz_1898_, lean_object* v_i_1899_, lean_object* v_bs_1900_){
_start:
{
size_t v_sz_boxed_1901_; size_t v_i_boxed_1902_; lean_object* v_res_1903_; 
v_sz_boxed_1901_ = lean_unbox_usize(v_sz_1898_);
lean_dec(v_sz_1898_);
v_i_boxed_1902_ = lean_unbox_usize(v_i_1899_);
lean_dec(v_i_1899_);
v_res_1903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(v_sz_boxed_1901_, v_i_boxed_1902_, v_bs_1900_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_a_1904_){
_start:
{
size_t v_sz_1905_; size_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_sz_1905_ = lean_array_size(v_a_1904_);
v___x_1906_ = ((size_t)0ULL);
v___x_1907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3_spec__6(v_sz_1905_, v___x_1906_, v_a_1904_);
v___x_1908_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_env_1909_, uint8_t v___x_1910_, lean_object* v_incrFile_1911_, lean_object* v_snapToSave_1912_){
_start:
{
lean_object* v___x_1914_; lean_object* v_regions_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1914_ = l_Lean_Environment_header(v_env_1909_);
v_regions_1915_ = lean_ctor_get(v___x_1914_, 2);
lean_inc_ref(v_regions_1915_);
lean_dec_ref(v___x_1914_);
v___x_1916_ = l_Lean_getRegularInitAttrModIdxs(v_env_1909_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_snapToSave_1912_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_compacted_region_save(v_incrFile_1911_, v___x_1918_, v___x_1917_, v_regions_1915_, v___x_1919_, v___x_1910_);
lean_dec_ref_known(v___x_1917_, 2);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1922_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1915_);
lean_dec_ref(v_regions_1915_);
v___x_1923_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1924_ = l_System_FilePath_addExtension(v_incrFile_1911_, v___x_1923_);
v___x_1925_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__3(v___x_1922_);
v___x_1926_ = l_Lean_Json_compress(v___x_1925_);
v___x_1927_ = l_IO_FS_writeFile(v___x_1924_, v___x_1926_);
lean_dec_ref(v___x_1926_);
lean_dec_ref(v___x_1924_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1935_; 
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; 
v_unused_1936_ = lean_ctor_get(v___x_1927_, 0);
lean_dec(v_unused_1936_);
v___x_1929_ = v___x_1927_;
v_isShared_1930_ = v_isSharedCheck_1935_;
goto v_resetjp_1928_;
}
else
{
lean_dec(v___x_1927_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1935_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_runtime_forget(v_a_1921_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1931_);
v___x_1933_ = v___x_1929_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
else
{
lean_dec(v_a_1921_);
return v___x_1927_;
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec_ref(v_regions_1915_);
lean_dec_ref(v_incrFile_1911_);
v_a_1937_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1920_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1920_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_env_1945_, lean_object* v___x_1946_, lean_object* v_incrFile_1947_, lean_object* v_snapToSave_1948_, lean_object* v___y_1949_){
_start:
{
uint8_t v___x_5993__boxed_1950_; lean_object* v_res_1951_; 
v___x_5993__boxed_1950_ = lean_unbox(v___x_1946_);
v_res_1951_ = l_Lean_Elab_runFrontend___lam__1(v_env_1945_, v___x_5993__boxed_1950_, v_incrFile_1947_, v_snapToSave_1948_);
lean_dec_ref(v_env_1945_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_fileMap_1952_, lean_object* v_env_1953_, lean_object* v___x_1954_, lean_object* v_opts_1955_, lean_object* v_val_1956_, uint8_t v___x_1957_, uint8_t v_a_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1960_ = l_Lean_Linter_recordLints(v_fileMap_1952_, v_env_1953_, v___x_1954_);
v___x_1961_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1962_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1955_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_writeModule(v___x_1960_, v_val_1956_, v___x_1957_);
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_writeModule(v___x_1960_, v_val_1956_, v_a_1958_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_fileMap_1965_, lean_object* v_env_1966_, lean_object* v___x_1967_, lean_object* v_opts_1968_, lean_object* v_val_1969_, lean_object* v___x_1970_, lean_object* v_a_1971_, lean_object* v___y_1972_){
_start:
{
uint8_t v___x_6064__boxed_1973_; uint8_t v_a_6065__boxed_1974_; lean_object* v_res_1975_; 
v___x_6064__boxed_1973_ = lean_unbox(v___x_1970_);
v_a_6065__boxed_1974_ = lean_unbox(v_a_1971_);
v_res_1975_ = l_Lean_Elab_runFrontend___lam__2(v_fileMap_1965_, v_env_1966_, v___x_1967_, v_opts_1968_, v_val_1969_, v___x_6064__boxed_1973_, v_a_6065__boxed_1974_);
lean_dec_ref(v_opts_1968_);
lean_dec_ref(v___x_1967_);
lean_dec_ref(v_fileMap_1965_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1976_, size_t v_i_1977_, size_t v_stop_1978_, lean_object* v_b_1979_){
_start:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_usize_dec_eq(v_i_1977_, v_stop_1978_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_array_uget_borrowed(v_as_1976_, v_i_1977_);
lean_inc(v___x_1982_);
v___x_1983_ = lean_load_dynlib(v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; size_t v___x_1985_; size_t v___x_1986_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1983_, 1);
v___x_1985_ = ((size_t)1ULL);
v___x_1986_ = lean_usize_add(v_i_1977_, v___x_1985_);
v_i_1977_ = v___x_1986_;
v_b_1979_ = v_a_1984_;
goto _start;
}
else
{
return v___x_1983_;
}
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1988_, 0, v_b_1979_);
return v___x_1988_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_1989_, lean_object* v_i_1990_, lean_object* v_stop_1991_, lean_object* v_b_1992_, lean_object* v___y_1993_){
_start:
{
size_t v_i_boxed_1994_; size_t v_stop_boxed_1995_; lean_object* v_res_1996_; 
v_i_boxed_1994_ = lean_unbox_usize(v_i_1990_);
lean_dec(v_i_1990_);
v_stop_boxed_1995_ = lean_unbox_usize(v_stop_1991_);
lean_dec(v_stop_1991_);
v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_1989_, v_i_boxed_1994_, v_stop_boxed_1995_, v_b_1992_);
lean_dec_ref(v_as_1989_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_setup_x3f_1997_, lean_object* v___f_1998_, lean_object* v___x_1999_, lean_object* v_plugins_2000_, uint32_t v_trustLevel_2001_, uint8_t v___x_2002_, lean_object* v_mainModuleName_2003_, lean_object* v_stx_2004_, lean_object* v___y_2005_){
_start:
{
uint8_t v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; 
if (lean_obj_tag(v_setup_x3f_1997_) == 1)
{
lean_object* v_val_2021_; lean_object* v_name_2022_; lean_object* v_package_x3f_2023_; uint8_t v_isModule_2024_; lean_object* v_imports_x3f_2025_; lean_object* v_importArts_2026_; lean_object* v_dynlibs_2027_; lean_object* v_plugins_2028_; lean_object* v_options_2029_; lean_object* v___y_2036_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
lean_dec(v_mainModuleName_2003_);
v_val_2021_ = lean_ctor_get(v_setup_x3f_1997_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v_setup_x3f_1997_, 1);
v_name_2022_ = lean_ctor_get(v_val_2021_, 0);
lean_inc(v_name_2022_);
v_package_x3f_2023_ = lean_ctor_get(v_val_2021_, 1);
lean_inc(v_package_x3f_2023_);
v_isModule_2024_ = lean_ctor_get_uint8(v_val_2021_, sizeof(void*)*7);
v_imports_x3f_2025_ = lean_ctor_get(v_val_2021_, 2);
lean_inc(v_imports_x3f_2025_);
v_importArts_2026_ = lean_ctor_get(v_val_2021_, 3);
lean_inc(v_importArts_2026_);
v_dynlibs_2027_ = lean_ctor_get(v_val_2021_, 4);
lean_inc_ref(v_dynlibs_2027_);
v_plugins_2028_ = lean_ctor_get(v_val_2021_, 5);
lean_inc_ref(v_plugins_2028_);
v_options_2029_ = lean_ctor_get(v_val_2021_, 6);
lean_inc(v_options_2029_);
lean_dec(v_val_2021_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_array_get_size(v_dynlibs_2027_);
v___x_2047_ = lean_nat_dec_lt(v___x_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_dec_ref(v_dynlibs_2027_);
goto v___jp_2030_;
}
else
{
lean_object* v___x_2048_; uint8_t v___x_2049_; 
v___x_2048_ = lean_box(0);
v___x_2049_ = lean_nat_dec_le(v___x_2046_, v___x_2046_);
if (v___x_2049_ == 0)
{
if (v___x_2047_ == 0)
{
lean_dec_ref(v_dynlibs_2027_);
goto v___jp_2030_;
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2046_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2027_, v___x_2050_, v___x_2051_, v___x_2048_);
lean_dec_ref(v_dynlibs_2027_);
v___y_2036_ = v___x_2052_;
goto v___jp_2035_;
}
}
else
{
size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = lean_usize_of_nat(v___x_2046_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2027_, v___x_2053_, v___x_2054_, v___x_2048_);
lean_dec_ref(v_dynlibs_2027_);
v___y_2036_ = v___x_2055_;
goto v___jp_2035_;
}
}
v___jp_2030_:
{
uint8_t v___x_2031_; uint8_t v___x_2032_; 
v___x_2031_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2004_);
v___x_2032_ = lean_strict_or(v_isModule_2024_, v___x_2031_);
if (lean_obj_tag(v_imports_x3f_2025_) == 0)
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2004_, v___x_2002_);
v___y_2008_ = v___x_2032_;
v___y_2009_ = v_package_x3f_2023_;
v___y_2010_ = v_plugins_2028_;
v___y_2011_ = v_options_2029_;
v___y_2012_ = v_importArts_2026_;
v___y_2013_ = v_name_2022_;
v___y_2014_ = v___x_2033_;
goto v___jp_2007_;
}
else
{
lean_object* v_val_2034_; 
lean_dec(v_stx_2004_);
v_val_2034_ = lean_ctor_get(v_imports_x3f_2025_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v_imports_x3f_2025_, 1);
v___y_2008_ = v___x_2032_;
v___y_2009_ = v_package_x3f_2023_;
v___y_2010_ = v_plugins_2028_;
v___y_2011_ = v_options_2029_;
v___y_2012_ = v_importArts_2026_;
v___y_2013_ = v_name_2022_;
v___y_2014_ = v_val_2034_;
goto v___jp_2007_;
}
}
v___jp_2035_:
{
if (lean_obj_tag(v___y_2036_) == 0)
{
lean_dec_ref_known(v___y_2036_, 1);
goto v___jp_2030_;
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_options_2029_);
lean_dec_ref(v_plugins_2028_);
lean_dec(v_importArts_2026_);
lean_dec(v_imports_x3f_2025_);
lean_dec(v_package_x3f_2023_);
lean_dec(v_name_2022_);
lean_dec(v_stx_2004_);
lean_dec_ref(v_plugins_2000_);
lean_dec_ref(v___x_1999_);
lean_dec_ref(v___f_1998_);
v_a_2037_ = lean_ctor_get(v___y_2036_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___y_2036_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___y_2036_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___y_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
else
{
lean_object* v___x_2056_; uint8_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec_ref(v___f_1998_);
lean_dec(v_setup_x3f_1997_);
v___x_2056_ = lean_box(0);
v___x_2057_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2004_);
v___x_2058_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2004_, v___x_2002_);
v___x_2059_ = lean_box(1);
v___x_2060_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2060_, 0, v_mainModuleName_2003_);
lean_ctor_set(v___x_2060_, 1, v___x_2056_);
lean_ctor_set(v___x_2060_, 2, v___x_2058_);
lean_ctor_set(v___x_2060_, 3, v___x_1999_);
lean_ctor_set(v___x_2060_, 4, v___x_2059_);
lean_ctor_set(v___x_2060_, 5, v_plugins_2000_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*6 + 4, v___x_2057_);
lean_ctor_set_uint32(v___x_2060_, sizeof(void*)*6, v_trustLevel_2001_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
return v___x_2062_;
}
v___jp_2007_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2015_ = l_Lean_LeanOptions_toOptions(v___y_2011_);
v___x_2016_ = l_Lean_Options_mergeBy(v___f_1998_, v___x_1999_, v___x_2015_);
v___x_2017_ = l_Array_append___redArg(v_plugins_2000_, v___y_2010_);
lean_dec_ref(v___y_2010_);
v___x_2018_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2018_, 0, v___y_2013_);
lean_ctor_set(v___x_2018_, 1, v___y_2009_);
lean_ctor_set(v___x_2018_, 2, v___y_2014_);
lean_ctor_set(v___x_2018_, 3, v___x_2016_);
lean_ctor_set(v___x_2018_, 4, v___y_2012_);
lean_ctor_set(v___x_2018_, 5, v___x_2017_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*6 + 4, v___y_2008_);
lean_ctor_set_uint32(v___x_2018_, sizeof(void*)*6, v_trustLevel_2001_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_setup_x3f_2063_, lean_object* v___f_2064_, lean_object* v___x_2065_, lean_object* v_plugins_2066_, lean_object* v_trustLevel_2067_, lean_object* v___x_2068_, lean_object* v_mainModuleName_2069_, lean_object* v_stx_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
uint32_t v_trustLevel_boxed_2073_; uint8_t v___x_6109__boxed_2074_; lean_object* v_res_2075_; 
v_trustLevel_boxed_2073_ = lean_unbox_uint32(v_trustLevel_2067_);
lean_dec(v_trustLevel_2067_);
v___x_6109__boxed_2074_ = lean_unbox(v___x_2068_);
v_res_2075_ = l_Lean_Elab_runFrontend___lam__3(v_setup_x3f_2063_, v___f_2064_, v___x_2065_, v_plugins_2066_, v_trustLevel_boxed_2073_, v___x_6109__boxed_2074_, v_mainModuleName_2069_, v_stx_2070_, v___y_2071_);
lean_dec_ref(v___y_2071_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_val_2076_, lean_object* v_initModIdxs_2077_, lean_object* v___x_2078_){
_start:
{
lean_object* v_cmdState_2080_; lean_object* v_env_2081_; lean_object* v___x_2082_; 
v_cmdState_2080_ = lean_ctor_get(v_val_2076_, 0);
lean_inc_ref(v_cmdState_2080_);
lean_dec_ref(v_val_2076_);
v_env_2081_ = lean_ctor_get(v_cmdState_2080_, 0);
lean_inc_ref(v_env_2081_);
lean_dec_ref(v_cmdState_2080_);
v___x_2082_ = l_Lean_runInitAttrsForModules(v_env_2081_, v_initModIdxs_2077_, v___x_2078_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_val_2083_, lean_object* v_initModIdxs_2084_, lean_object* v___x_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Lean_Elab_runFrontend___lam__4(v_val_2083_, v_initModIdxs_2084_, v___x_2085_);
lean_dec_ref(v___x_2085_);
lean_dec_ref(v_initModIdxs_2084_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2091_, lean_object* v_k_2092_, uint8_t v_v_2093_){
_start:
{
lean_object* v_map_2094_; uint8_t v_hasTrace_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2109_; 
v_map_2094_ = lean_ctor_get(v_o_2091_, 0);
v_hasTrace_2095_ = lean_ctor_get_uint8(v_o_2091_, sizeof(void*)*1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_o_2091_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2097_ = v_o_2091_;
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_map_2094_);
lean_dec(v_o_2091_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2109_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2099_, 0, v_v_2093_);
lean_inc(v_k_2092_);
v___x_2100_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2092_, v___x_2099_, v_map_2094_);
if (v_hasTrace_2095_ == 0)
{
lean_object* v___x_2101_; uint8_t v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2102_ = l_Lean_Name_isPrefixOf(v___x_2101_, v_k_2092_);
lean_dec(v_k_2092_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2104_ = v___x_2097_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2100_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*1, v___x_2102_);
return v___x_2104_;
}
}
else
{
lean_object* v___x_2107_; 
lean_dec(v_k_2092_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2107_ = v___x_2097_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2100_);
lean_ctor_set_uint8(v_reuseFailAlloc_2108_, sizeof(void*)*1, v_hasTrace_2095_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2110_, lean_object* v_k_2111_, lean_object* v_v_2112_){
_start:
{
uint8_t v_v_boxed_2113_; lean_object* v_res_2114_; 
v_v_boxed_2113_ = lean_unbox(v_v_2112_);
v_res_2114_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2110_, v_k_2111_, v_v_boxed_2113_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2115_, lean_object* v_opt_2116_, uint8_t v_val_2117_){
_start:
{
lean_object* v_name_2118_; lean_object* v___x_2119_; 
v_name_2118_ = lean_ctor_get(v_opt_2116_, 0);
lean_inc(v_name_2118_);
lean_dec_ref(v_opt_2116_);
v___x_2119_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2115_, v_name_2118_, v_val_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2120_, lean_object* v_opt_2121_, lean_object* v_val_2122_){
_start:
{
uint8_t v_val_boxed_2123_; lean_object* v_res_2124_; 
v_val_boxed_2123_ = lean_unbox(v_val_2122_);
v_res_2124_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2120_, v_opt_2121_, v_val_boxed_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2125_, lean_object* v_opt_2126_, uint8_t v_val_2127_){
_start:
{
lean_object* v_name_2128_; lean_object* v_map_2129_; uint8_t v___x_2130_; 
v_name_2128_ = lean_ctor_get(v_opt_2126_, 0);
v_map_2129_ = lean_ctor_get(v_opts_2125_, 0);
v___x_2130_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2128_, v_map_2129_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2125_, v_opt_2126_, v_val_2127_);
return v___x_2131_;
}
else
{
lean_dec_ref(v_opt_2126_);
return v_opts_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2132_, lean_object* v_opt_2133_, lean_object* v_val_2134_){
_start:
{
uint8_t v_val_boxed_2135_; lean_object* v_res_2136_; 
v_val_boxed_2135_ = lean_unbox(v_val_2134_);
v_res_2136_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2132_, v_opt_2133_, v_val_boxed_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_bs_2139_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2140_ == 0)
{
return v_bs_2139_;
}
else
{
lean_object* v_v_2141_; lean_object* v_traces_2142_; lean_object* v___x_2143_; lean_object* v_bs_x27_2144_; size_t v___x_2145_; size_t v___x_2146_; lean_object* v___x_2147_; 
v_v_2141_ = lean_array_uget_borrowed(v_bs_2139_, v_i_2138_);
v_traces_2142_ = lean_ctor_get(v_v_2141_, 3);
lean_inc_ref(v_traces_2142_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v_bs_x27_2144_ = lean_array_uset(v_bs_2139_, v_i_2138_, v___x_2143_);
v___x_2145_ = ((size_t)1ULL);
v___x_2146_ = lean_usize_add(v_i_2138_, v___x_2145_);
v___x_2147_ = lean_array_uset(v_bs_x27_2144_, v_i_2138_, v_traces_2142_);
v_i_2138_ = v___x_2146_;
v_bs_2139_ = v___x_2147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2149_, lean_object* v_i_2150_, lean_object* v_bs_2151_){
_start:
{
size_t v_sz_boxed_2152_; size_t v_i_boxed_2153_; lean_object* v_res_2154_; 
v_sz_boxed_2152_ = lean_unbox_usize(v_sz_2149_);
lean_dec(v_sz_2149_);
v_i_boxed_2153_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2152_, v_i_boxed_2153_, v_bs_2151_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = l_Lean_Language_Snapshot_transform(v_s_2157_, v___y_2158_);
v___x_2160_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2162_, v___y_2163_);
lean_dec_ref(v___y_2163_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___f_2168_; lean_object* v___x_2169_; 
v___f_2168_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2169_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2166_, v___f_2168_, v_a_2167_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2170_, v_a_2171_);
lean_dec_ref(v_a_2171_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2177_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2174_, v___x_2176_, v_a_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2178_, lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2178_, v_a_2179_);
lean_dec_ref(v_a_2179_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_toSnapshot_2183_; lean_object* v_metaSnap_2184_; lean_object* v_result_x3f_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___y_2189_; 
v_toSnapshot_2183_ = lean_ctor_get(v_s_2181_, 0);
lean_inc_ref(v_toSnapshot_2183_);
v_metaSnap_2184_ = lean_ctor_get(v_s_2181_, 1);
lean_inc_ref(v_metaSnap_2184_);
v_result_x3f_2185_ = lean_ctor_get(v_s_2181_, 2);
lean_inc(v_result_x3f_2185_);
lean_dec_ref(v_s_2181_);
v___x_2186_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2183_, v___y_2182_);
v___x_2187_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2184_, v___y_2182_);
if (lean_obj_tag(v_result_x3f_2185_) == 0)
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_box(0);
v___y_2189_ = v___x_2195_;
goto v___jp_2188_;
}
else
{
lean_object* v_val_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2205_; 
v_val_2196_ = lean_ctor_get(v_result_x3f_2185_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v_result_x3f_2185_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2198_ = v_result_x3f_2185_;
v_isShared_2199_ = v_isSharedCheck_2205_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_val_2196_);
lean_dec(v_result_x3f_2185_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2205_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v_firstCmdSnap_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v_firstCmdSnap_2200_ = lean_ctor_get(v_val_2196_, 1);
lean_inc_ref(v_firstCmdSnap_2200_);
lean_dec(v_val_2196_);
v___x_2201_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2200_, v___y_2182_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2201_);
v___x_2203_ = v___x_2198_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
v___y_2189_ = v___x_2203_;
goto v___jp_2188_;
}
}
}
v___jp_2188_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = lean_mk_empty_array_with_capacity(v___x_2190_);
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2187_);
v___x_2193_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2189_, v___x_2192_);
v___x_2194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2186_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2206_, v___y_2207_);
lean_dec_ref(v___y_2207_);
return v_res_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v___f_2212_; lean_object* v___x_2213_; 
v___f_2212_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2213_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2210_, v___f_2212_, v_a_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2214_, v_a_2215_);
lean_dec_ref(v_a_2215_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2217_){
_start:
{
lean_object* v_toSnapshot_2218_; lean_object* v_metaSnap_2219_; lean_object* v_result_x3f_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___y_2225_; 
v_toSnapshot_2218_ = lean_ctor_get(v_a_2217_, 0);
lean_inc_ref(v_toSnapshot_2218_);
v_metaSnap_2219_ = lean_ctor_get(v_a_2217_, 1);
lean_inc_ref(v_metaSnap_2219_);
v_result_x3f_2220_ = lean_ctor_get(v_a_2217_, 4);
lean_inc(v_result_x3f_2220_);
lean_dec_ref(v_a_2217_);
v___x_2221_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2222_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2218_, v___x_2221_);
v___x_2223_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2219_, v___x_2221_);
if (lean_obj_tag(v_result_x3f_2220_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_box(0);
v___y_2225_ = v___x_2231_;
goto v___jp_2224_;
}
else
{
lean_object* v_val_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2241_; 
v_val_2232_ = lean_ctor_get(v_result_x3f_2220_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v_result_x3f_2220_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2234_ = v_result_x3f_2220_;
v_isShared_2235_ = v_isSharedCheck_2241_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_val_2232_);
lean_dec(v_result_x3f_2220_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2241_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v_processedSnap_2236_; lean_object* v___x_2237_; lean_object* v___x_2239_; 
v_processedSnap_2236_ = lean_ctor_get(v_val_2232_, 1);
lean_inc_ref(v_processedSnap_2236_);
lean_dec(v_val_2232_);
v___x_2237_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2236_, v___x_2221_);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2237_);
v___x_2239_ = v___x_2234_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
v___y_2225_ = v___x_2239_;
goto v___jp_2224_;
}
}
}
v___jp_2224_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2226_ = lean_unsigned_to_nat(1u);
v___x_2227_ = lean_mk_empty_array_with_capacity(v___x_2226_);
v___x_2228_ = lean_array_push(v___x_2227_, v___x_2223_);
v___x_2229_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2225_, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2222_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_as_2242_, size_t v_i_2243_, size_t v_stop_2244_, lean_object* v_b_2245_){
_start:
{
uint8_t v___x_2246_; 
v___x_2246_ = lean_usize_dec_eq(v_i_2243_, v_stop_2244_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; 
v___x_2247_ = lean_array_uget_borrowed(v_as_2242_, v_i_2243_);
v___x_2248_ = 2;
v___x_2249_ = lean_box(v___x_2248_);
lean_inc(v___x_2247_);
v___x_2250_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2247_, v___x_2249_, v_b_2245_);
v___x_2251_ = ((size_t)1ULL);
v___x_2252_ = lean_usize_add(v_i_2243_, v___x_2251_);
v_i_2243_ = v___x_2252_;
v_b_2245_ = v___x_2250_;
goto _start;
}
else
{
return v_b_2245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8___boxed(lean_object* v_as_2254_, lean_object* v_i_2255_, lean_object* v_stop_2256_, lean_object* v_b_2257_){
_start:
{
size_t v_i_boxed_2258_; size_t v_stop_boxed_2259_; lean_object* v_res_2260_; 
v_i_boxed_2258_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_stop_boxed_2259_ = lean_unbox_usize(v_stop_2256_);
lean_dec(v_stop_2256_);
v_res_2260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_as_2254_, v_i_boxed_2258_, v_stop_boxed_2259_, v_b_2257_);
lean_dec_ref(v_as_2254_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2261_, size_t v_i_2262_, size_t v_stop_2263_, lean_object* v_b_2264_){
_start:
{
lean_object* v___y_2266_; uint8_t v___x_2270_; 
v___x_2270_ = lean_usize_dec_eq(v_i_2262_, v_stop_2263_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v_infoTree_x3f_2272_; 
v___x_2271_ = lean_array_uget_borrowed(v_as_2261_, v_i_2262_);
v_infoTree_x3f_2272_ = lean_ctor_get(v___x_2271_, 2);
if (lean_obj_tag(v_infoTree_x3f_2272_) == 1)
{
lean_object* v_val_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v_val_2273_ = lean_ctor_get(v_infoTree_x3f_2272_, 0);
v___x_2274_ = lean_unsigned_to_nat(1u);
v___x_2275_ = lean_mk_empty_array_with_capacity(v___x_2274_);
lean_inc(v_val_2273_);
v___x_2276_ = lean_array_push(v___x_2275_, v_val_2273_);
v___x_2277_ = l_Array_append___redArg(v_b_2264_, v___x_2276_);
lean_dec_ref(v___x_2276_);
v___y_2266_ = v___x_2277_;
goto v___jp_2265_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2279_ = l_Array_append___redArg(v_b_2264_, v___x_2278_);
v___y_2266_ = v___x_2279_;
goto v___jp_2265_;
}
}
else
{
return v_b_2264_;
}
v___jp_2265_:
{
size_t v___x_2267_; size_t v___x_2268_; 
v___x_2267_ = ((size_t)1ULL);
v___x_2268_ = lean_usize_add(v_i_2262_, v___x_2267_);
v_i_2262_ = v___x_2268_;
v_b_2264_ = v___y_2266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2280_, lean_object* v_i_2281_, lean_object* v_stop_2282_, lean_object* v_b_2283_){
_start:
{
size_t v_i_boxed_2284_; size_t v_stop_boxed_2285_; lean_object* v_res_2286_; 
v_i_boxed_2284_ = lean_unbox_usize(v_i_2281_);
lean_dec(v_i_2281_);
v_stop_boxed_2285_ = lean_unbox_usize(v_stop_2282_);
lean_dec(v_stop_2282_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2280_, v_i_boxed_2284_, v_stop_boxed_2285_, v_b_2283_);
lean_dec_ref(v_as_2280_);
return v_res_2286_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__1(void){
_start:
{
lean_object* v___x_2288_; double v___x_2289_; 
v___x_2288_ = lean_unsigned_to_nat(1000000000u);
v___x_2289_ = lean_float_of_nat(v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2291_, lean_object* v_opts_2292_, lean_object* v_fileName_2293_, lean_object* v_mainModuleName_2294_, uint32_t v_trustLevel_2295_, lean_object* v_oleanFileName_x3f_2296_, lean_object* v_ileanFileName_x3f_2297_, uint8_t v_jsonOutput_2298_, lean_object* v_errorOnKinds_2299_, lean_object* v_plugins_2300_, uint8_t v_printStats_2301_, lean_object* v_setup_x3f_2302_, lean_object* v_incrSaveFileName_x3f_2303_, lean_object* v_incrLoadFileName_x3f_2304_, lean_object* v_incrHeaderSaveFileName_x3f_2305_){
_start:
{
lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___x_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; double v___x_2316_; double v___x_2317_; double v___x_2318_; uint8_t v___x_2319_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v___y_2443_; lean_object* v___y_2444_; uint8_t v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2449_; lean_object* v___y_2450_; lean_object* v___y_2451_; uint8_t v___y_2452_; lean_object* v___y_2475_; lean_object* v___y_2476_; uint8_t v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; uint8_t v___y_2484_; lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v_a_2566_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v___y_2587_; 
v___x_2313_ = lean_io_mono_nanos_now();
v___f_2314_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_2315_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2316_ = lean_float_of_nat(v___x_2313_);
v___x_2317_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__1, &l_Lean_Elab_runFrontend___closed__1_once, _init_l_Lean_Elab_runFrontend___closed__1);
v___x_2318_ = lean_float_div(v___x_2316_, v___x_2317_);
v___x_2319_ = 1;
v___x_2382_ = lean_string_utf8_byte_size(v_input_2291_);
v___x_2383_ = l_Lean_Parser_mkInputContext___redArg(v_input_2291_, v_fileName_2293_, v___x_2319_, v___x_2382_);
v___x_2585_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2303_) == 0)
{
v___y_2587_ = v___x_2319_;
goto v___jp_2586_;
}
else
{
uint8_t v___x_2623_; 
v___x_2623_ = 0;
v___y_2587_ = v___x_2623_;
goto v___jp_2586_;
}
v___jp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = lean_runtime_forget(v___y_2308_);
v___x_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___y_2309_);
v___x_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
return v___x_2312_;
}
v___jp_2320_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = l_Lean_trace_profiler_output;
v___x_2326_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2323_, v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 1)
{
lean_object* v_val_2327_; lean_object* v___x_2328_; size_t v_sz_2329_; size_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v___y_2324_);
v_val_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_val_2327_);
lean_dec_ref_known(v___x_2326_, 1);
lean_inc_ref(v___y_2321_);
v___x_2328_ = l_Lean_Language_SnapshotTree_getAll(v___y_2321_);
v_sz_2329_ = lean_array_size(v___x_2328_);
v___x_2330_ = ((size_t)0ULL);
v___x_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2329_, v___x_2330_, v___x_2328_);
v___x_2332_ = l_Lean_Name_toString(v_mainModuleName_2294_, v___x_2319_);
v___x_2333_ = l_Lean_Firefox_Profile_export(v___x_2332_, v___x_2318_, v___x_2331_, v___y_2323_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v___x_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2335_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2334_);
v___x_2336_ = l_Lean_Json_compress(v___x_2335_);
v___x_2337_ = l_IO_FS_writeFile(v_val_2327_, v___x_2336_);
lean_dec_ref(v___x_2336_);
lean_dec(v_val_2327_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_dec_ref_known(v___x_2337_, 1);
v___y_2308_ = v___y_2321_;
v___y_2309_ = v___y_2322_;
goto v___jp_2307_;
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___y_2322_);
lean_dec_ref(v___y_2321_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v_val_2327_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v___y_2321_);
v_a_2346_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2333_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2333_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
lean_dec(v___x_2326_);
v___x_2354_ = l_Lean_trace_profiler_serve;
v___x_2355_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2324_, v___x_2354_);
lean_dec_ref(v___y_2324_);
if (v___x_2355_ == 0)
{
lean_dec_ref(v___y_2323_);
lean_dec(v_mainModuleName_2294_);
v___y_2308_ = v___y_2321_;
v___y_2309_ = v___y_2322_;
goto v___jp_2307_;
}
else
{
lean_object* v___x_2356_; size_t v_sz_2357_; size_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_inc_ref(v___y_2321_);
v___x_2356_ = l_Lean_Language_SnapshotTree_getAll(v___y_2321_);
v_sz_2357_ = lean_array_size(v___x_2356_);
v___x_2358_ = ((size_t)0ULL);
v___x_2359_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2357_, v___x_2358_, v___x_2356_);
v___x_2360_ = l_Lean_Name_toString(v_mainModuleName_2294_, v___x_2319_);
v___x_2361_ = l_Lean_Firefox_Profile_export(v___x_2360_, v___x_2318_, v___x_2359_, v___y_2323_);
lean_dec_ref(v___y_2323_);
lean_dec_ref(v___x_2359_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2362_);
v___x_2364_ = l_Lean_Json_compress(v___x_2363_);
v___x_2365_ = l_Lean_Firefox_Profile_serve(v___x_2364_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_dec_ref_known(v___x_2365_, 1);
v___y_2308_ = v___y_2321_;
v___y_2309_ = v___y_2322_;
goto v___jp_2307_;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec_ref(v___y_2322_);
lean_dec_ref(v___y_2321_);
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2365_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2365_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v___y_2322_);
lean_dec_ref(v___y_2321_);
v_a_2374_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2361_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2361_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
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
}
}
v___jp_2384_:
{
lean_object* v_fileMap_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v_stx_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2418_; 
v_fileMap_2392_ = lean_ctor_get(v___x_2383_, 2);
lean_inc_ref(v_fileMap_2392_);
lean_dec_ref(v___x_2383_);
v___x_2393_ = 0;
v___x_2394_ = l_Lean_Server_findModuleRefs(v_fileMap_2392_, v___y_2391_, v___x_2393_, v___x_2393_);
lean_dec_ref(v___y_2391_);
v___x_2395_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2394_);
v_fst_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_fst_2396_);
v_snd_2397_ = lean_ctor_get(v___x_2395_, 1);
lean_inc(v_snd_2397_);
lean_dec_ref(v___x_2395_);
v_stx_2398_ = lean_ctor_get(v___y_2390_, 3);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___y_2390_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; lean_object* v_unused_2420_; lean_object* v_unused_2421_; lean_object* v_unused_2422_; 
v_unused_2419_ = lean_ctor_get(v___y_2390_, 4);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v___y_2390_, 2);
lean_dec(v_unused_2420_);
v_unused_2421_ = lean_ctor_get(v___y_2390_, 1);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v___y_2390_, 0);
lean_dec(v_unused_2422_);
v___x_2400_ = v___y_2390_;
v_isShared_2401_ = v_isSharedCheck_2418_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_stx_2398_);
lean_dec(v___y_2390_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2418_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2402_ = lean_unsigned_to_nat(5u);
v___x_2403_ = l_Lean_Server_collectImports(v_stx_2398_);
lean_inc(v_mainModuleName_2294_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 4, v_snd_2397_);
lean_ctor_set(v___x_2400_, 3, v_fst_2396_);
lean_ctor_set(v___x_2400_, 2, v___x_2403_);
lean_ctor_set(v___x_2400_, 1, v_mainModuleName_2294_);
lean_ctor_set(v___x_2400_, 0, v___x_2402_);
v___x_2405_ = v___x_2400_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_mainModuleName_2294_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_fst_2396_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v_snd_2397_);
v___x_2405_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2405_);
v___x_2407_ = l_Lean_Json_compress(v___x_2406_);
v___x_2408_ = l_IO_FS_writeFile(v___y_2385_, v___x_2407_);
lean_dec_ref(v___x_2407_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_dec_ref_known(v___x_2408_, 1);
v___y_2321_ = v___y_2386_;
v___y_2322_ = v___y_2387_;
v___y_2323_ = v___y_2388_;
v___y_2324_ = v___y_2389_;
goto v___jp_2320_;
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec_ref(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v_mainModuleName_2294_);
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
}
v___jp_2423_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2297_) == 1)
{
lean_object* v_val_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; uint8_t v___x_2434_; 
v_val_2430_ = lean_ctor_get(v_ileanFileName_x3f_2297_, 0);
lean_inc_ref(v___y_2424_);
v___x_2431_ = l_Lean_Language_SnapshotTree_getAll(v___y_2424_);
v___x_2432_ = lean_mk_empty_array_with_capacity(v___y_2429_);
v___x_2433_ = lean_array_get_size(v___x_2431_);
v___x_2434_ = lean_nat_dec_lt(v___y_2429_, v___x_2433_);
lean_dec(v___y_2429_);
if (v___x_2434_ == 0)
{
lean_dec_ref(v___x_2431_);
v___y_2385_ = v_val_2430_;
v___y_2386_ = v___y_2424_;
v___y_2387_ = v___y_2425_;
v___y_2388_ = v___y_2426_;
v___y_2389_ = v___y_2428_;
v___y_2390_ = v___y_2427_;
v___y_2391_ = v___x_2432_;
goto v___jp_2384_;
}
else
{
uint8_t v___x_2435_; 
v___x_2435_ = lean_nat_dec_le(v___x_2433_, v___x_2433_);
if (v___x_2435_ == 0)
{
if (v___x_2434_ == 0)
{
lean_dec_ref(v___x_2431_);
v___y_2385_ = v_val_2430_;
v___y_2386_ = v___y_2424_;
v___y_2387_ = v___y_2425_;
v___y_2388_ = v___y_2426_;
v___y_2389_ = v___y_2428_;
v___y_2390_ = v___y_2427_;
v___y_2391_ = v___x_2432_;
goto v___jp_2384_;
}
else
{
size_t v___x_2436_; size_t v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = ((size_t)0ULL);
v___x_2437_ = lean_usize_of_nat(v___x_2433_);
v___x_2438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2431_, v___x_2436_, v___x_2437_, v___x_2432_);
lean_dec_ref(v___x_2431_);
v___y_2385_ = v_val_2430_;
v___y_2386_ = v___y_2424_;
v___y_2387_ = v___y_2425_;
v___y_2388_ = v___y_2426_;
v___y_2389_ = v___y_2428_;
v___y_2390_ = v___y_2427_;
v___y_2391_ = v___x_2438_;
goto v___jp_2384_;
}
}
else
{
size_t v___x_2439_; size_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = ((size_t)0ULL);
v___x_2440_ = lean_usize_of_nat(v___x_2433_);
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2431_, v___x_2439_, v___x_2440_, v___x_2432_);
lean_dec_ref(v___x_2431_);
v___y_2385_ = v_val_2430_;
v___y_2386_ = v___y_2424_;
v___y_2387_ = v___y_2425_;
v___y_2388_ = v___y_2426_;
v___y_2389_ = v___y_2428_;
v___y_2390_ = v___y_2427_;
v___y_2391_ = v___x_2441_;
goto v___jp_2384_;
}
}
}
else
{
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2427_);
lean_dec_ref(v___x_2383_);
v___y_2321_ = v___y_2424_;
v___y_2322_ = v___y_2425_;
v___y_2323_ = v___y_2426_;
v___y_2324_ = v___y_2428_;
goto v___jp_2320_;
}
}
v___jp_2442_:
{
if (v___y_2452_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2296_) == 1)
{
lean_object* v_val_2453_; lean_object* v_fileMap_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___f_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_val_2453_ = lean_ctor_get(v_oleanFileName_x3f_2296_, 0);
lean_inc(v_val_2453_);
lean_dec_ref_known(v_oleanFileName_x3f_2296_, 1);
v_fileMap_2454_ = lean_ctor_get(v___x_2383_, 2);
lean_inc_ref(v_fileMap_2454_);
v___x_2455_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__2));
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_mk_empty_array_with_capacity(v___y_2451_);
lean_inc_ref(v___y_2446_);
v___x_2458_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2446_, v___x_2456_, v___x_2457_);
v___x_2459_ = lean_box(v___x_2319_);
v___x_2460_ = lean_box(v___y_2445_);
v___f_2461_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2461_, 0, v_fileMap_2454_);
lean_closure_set(v___f_2461_, 1, v___y_2443_);
lean_closure_set(v___f_2461_, 2, v___x_2458_);
lean_closure_set(v___f_2461_, 3, v___y_2444_);
lean_closure_set(v___f_2461_, 4, v_val_2453_);
lean_closure_set(v___f_2461_, 5, v___x_2459_);
lean_closure_set(v___f_2461_, 6, v___x_2460_);
v___x_2462_ = lean_box(0);
v___x_2463_ = l_Lean_profileitIOUnsafe___redArg(v___x_2455_, v___y_2450_, v___f_2461_, v___x_2462_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_dec_ref_known(v___x_2463_, 1);
v___y_2424_ = v___y_2446_;
v___y_2425_ = v___y_2447_;
v___y_2426_ = v___y_2448_;
v___y_2427_ = v___y_2449_;
v___y_2428_ = v___y_2450_;
v___y_2429_ = v___y_2451_;
goto v___jp_2423_;
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec_ref(v___x_2383_);
lean_dec(v_mainModuleName_2294_);
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_oleanFileName_x3f_2296_);
v___y_2424_ = v___y_2446_;
v___y_2425_ = v___y_2447_;
v___y_2426_ = v___y_2448_;
v___y_2427_ = v___y_2449_;
v___y_2428_ = v___y_2450_;
v___y_2429_ = v___y_2451_;
goto v___jp_2423_;
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec_ref(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___x_2383_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
return v___x_2473_;
}
}
v___jp_2474_:
{
if (v_printStats_2301_ == 0)
{
v___y_2443_ = v___y_2475_;
v___y_2444_ = v___y_2476_;
v___y_2445_ = v___y_2477_;
v___y_2446_ = v___y_2478_;
v___y_2447_ = v___y_2479_;
v___y_2448_ = v___y_2480_;
v___y_2449_ = v___y_2482_;
v___y_2450_ = v___y_2481_;
v___y_2451_ = v___y_2483_;
v___y_2452_ = v___y_2484_;
goto v___jp_2442_;
}
else
{
lean_object* v___x_2485_; 
lean_inc_ref(v___y_2479_);
v___x_2485_ = l_Lean_Environment_displayStats(v___y_2479_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_dec_ref_known(v___x_2485_, 1);
v___y_2443_ = v___y_2475_;
v___y_2444_ = v___y_2476_;
v___y_2445_ = v___y_2477_;
v___y_2446_ = v___y_2478_;
v___y_2447_ = v___y_2479_;
v___y_2448_ = v___y_2480_;
v___y_2449_ = v___y_2482_;
v___y_2450_ = v___y_2481_;
v___y_2451_ = v___y_2483_;
v___y_2452_ = v___y_2484_;
goto v___jp_2442_;
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec_ref(v___x_2383_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
v___jp_2494_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2305_) == 1)
{
lean_object* v_val_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_val_2505_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2305_, 0);
lean_inc(v_val_2505_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2305_, 1);
lean_inc_ref(v___y_2502_);
v___x_2506_ = l_Lean_Language_Lean_truncateToHeader(v___y_2502_);
v___x_2507_ = lean_apply_3(v___y_2498_, v_val_2505_, v___x_2506_, lean_box(0));
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_dec_ref_known(v___x_2507_, 1);
lean_inc_ref(v___y_2496_);
v___y_2475_ = v___y_2495_;
v___y_2476_ = v___y_2496_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2499_;
v___y_2479_ = v___y_2500_;
v___y_2480_ = v___y_2501_;
v___y_2481_ = v___y_2496_;
v___y_2482_ = v___y_2502_;
v___y_2483_ = v___y_2503_;
v___y_2484_ = v___y_2504_;
goto v___jp_2474_;
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec_ref(v___x_2383_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
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
lean_dec_ref(v___y_2498_);
lean_dec(v_incrHeaderSaveFileName_x3f_2305_);
lean_inc_ref(v___y_2496_);
v___y_2475_ = v___y_2495_;
v___y_2476_ = v___y_2496_;
v___y_2477_ = v___y_2497_;
v___y_2478_ = v___y_2499_;
v___y_2479_ = v___y_2500_;
v___y_2480_ = v___y_2501_;
v___y_2481_ = v___y_2496_;
v___y_2482_ = v___y_2502_;
v___y_2483_ = v___y_2503_;
v___y_2484_ = v___y_2504_;
goto v___jp_2474_;
}
}
v___jp_2516_:
{
lean_object* v___x_2522_; 
lean_inc_ref(v___y_2517_);
v___x_2522_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2517_, v___y_2518_, v_jsonOutput_2298_, v___y_2521_);
lean_dec(v___y_2521_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2554_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2525_ = v___x_2522_;
v_isShared_2526_ = v_isSharedCheck_2554_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2554_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; 
lean_inc_ref(v___y_2519_);
v___x_2527_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2519_);
if (lean_obj_tag(v___x_2527_) == 1)
{
lean_object* v_val_2528_; lean_object* v_env_2529_; lean_object* v_scopes_2530_; lean_object* v___x_2531_; lean_object* v_opts_2532_; lean_object* v___x_2533_; lean_object* v___f_2534_; 
lean_del_object(v___x_2525_);
v_val_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_val_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v_env_2529_ = lean_ctor_get(v_val_2528_, 0);
lean_inc_ref_n(v_env_2529_, 2);
v_scopes_2530_ = lean_ctor_get(v_val_2528_, 2);
lean_inc(v_scopes_2530_);
lean_dec(v_val_2528_);
lean_inc(v___y_2520_);
v___x_2531_ = l_List_get_x21Internal___redArg(v___x_2315_, v_scopes_2530_, v___y_2520_);
lean_dec(v_scopes_2530_);
v_opts_2532_ = lean_ctor_get(v___x_2531_, 1);
lean_inc_ref(v_opts_2532_);
lean_dec(v___x_2531_);
v___x_2533_ = lean_box(v___x_2319_);
v___f_2534_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2534_, 0, v_env_2529_);
lean_closure_set(v___f_2534_, 1, v___x_2533_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2303_) == 1)
{
lean_object* v_val_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_val_2535_ = lean_ctor_get(v_incrSaveFileName_x3f_2303_, 0);
lean_inc(v_val_2535_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2303_, 1);
v___x_2536_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2517_);
lean_inc_ref(v___y_2519_);
v___x_2537_ = l_Lean_Elab_runFrontend___lam__1(v_env_2529_, v___x_2319_, v_val_2535_, v___y_2519_);
if (lean_obj_tag(v___x_2537_) == 0)
{
uint8_t v___x_2538_; uint8_t v___x_2539_; 
lean_dec_ref_known(v___x_2537_, 1);
v___x_2538_ = lean_unbox(v_a_2523_);
v___x_2539_ = lean_unbox(v_a_2523_);
lean_dec(v_a_2523_);
lean_inc_ref(v_env_2529_);
v___y_2495_ = v_env_2529_;
v___y_2496_ = v_opts_2532_;
v___y_2497_ = v___x_2538_;
v___y_2498_ = v___f_2534_;
v___y_2499_ = v___y_2517_;
v___y_2500_ = v_env_2529_;
v___y_2501_ = v___y_2518_;
v___y_2502_ = v___y_2519_;
v___y_2503_ = v___y_2520_;
v___y_2504_ = v___x_2539_;
goto v___jp_2494_;
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v___f_2534_);
lean_dec_ref(v_opts_2532_);
lean_dec_ref(v_env_2529_);
lean_dec(v_a_2523_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___x_2383_);
lean_dec(v_incrHeaderSaveFileName_x3f_2305_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v_a_2540_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2537_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2537_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
uint8_t v___x_2548_; uint8_t v___x_2549_; 
lean_dec(v_incrSaveFileName_x3f_2303_);
v___x_2548_ = lean_unbox(v_a_2523_);
v___x_2549_ = lean_unbox(v_a_2523_);
lean_dec(v_a_2523_);
lean_inc_ref(v_env_2529_);
v___y_2495_ = v_env_2529_;
v___y_2496_ = v_opts_2532_;
v___y_2497_ = v___x_2548_;
v___y_2498_ = v___f_2534_;
v___y_2499_ = v___y_2517_;
v___y_2500_ = v_env_2529_;
v___y_2501_ = v___y_2518_;
v___y_2502_ = v___y_2519_;
v___y_2503_ = v___y_2520_;
v___y_2504_ = v___x_2549_;
goto v___jp_2494_;
}
}
else
{
lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_dec(v___x_2527_);
lean_dec(v_a_2523_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___x_2383_);
lean_dec(v_incrHeaderSaveFileName_x3f_2305_);
lean_dec(v_incrSaveFileName_x3f_2303_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v___x_2550_ = lean_box(0);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2550_);
v___x_2552_ = v___x_2525_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v___x_2383_);
lean_dec(v_incrHeaderSaveFileName_x3f_2305_);
lean_dec(v_incrSaveFileName_x3f_2303_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v_a_2555_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2522_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2522_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
v___jp_2563_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2567_ = l_Lean_Language_Lean_process(v___y_2564_, v_a_2566_, v___x_2383_);
lean_inc_ref(v___x_2567_);
v___x_2568_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2567_);
v___x_2569_ = lean_box(1);
v___x_2570_ = lean_unsigned_to_nat(0u);
v___x_2571_ = lean_array_get_size(v_errorOnKinds_2299_);
v___x_2572_ = lean_nat_dec_lt(v___x_2570_, v___x_2571_);
if (v___x_2572_ == 0)
{
v___y_2517_ = v___x_2568_;
v___y_2518_ = v___y_2565_;
v___y_2519_ = v___x_2567_;
v___y_2520_ = v___x_2570_;
v___y_2521_ = v___x_2569_;
goto v___jp_2516_;
}
else
{
uint8_t v___x_2573_; 
v___x_2573_ = lean_nat_dec_le(v___x_2571_, v___x_2571_);
if (v___x_2573_ == 0)
{
if (v___x_2572_ == 0)
{
v___y_2517_ = v___x_2568_;
v___y_2518_ = v___y_2565_;
v___y_2519_ = v___x_2567_;
v___y_2520_ = v___x_2570_;
v___y_2521_ = v___x_2569_;
goto v___jp_2516_;
}
else
{
size_t v___x_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = lean_usize_of_nat(v___x_2571_);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_errorOnKinds_2299_, v___x_2574_, v___x_2575_, v___x_2569_);
v___y_2517_ = v___x_2568_;
v___y_2518_ = v___y_2565_;
v___y_2519_ = v___x_2567_;
v___y_2520_ = v___x_2570_;
v___y_2521_ = v___x_2576_;
goto v___jp_2516_;
}
}
else
{
size_t v___x_2577_; size_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = ((size_t)0ULL);
v___x_2578_ = lean_usize_of_nat(v___x_2571_);
v___x_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_errorOnKinds_2299_, v___x_2577_, v___x_2578_, v___x_2569_);
v___y_2517_ = v___x_2568_;
v___y_2518_ = v___y_2565_;
v___y_2519_ = v___x_2567_;
v___y_2520_ = v___x_2570_;
v___y_2521_ = v___x_2579_;
goto v___jp_2516_;
}
}
}
v___jp_2580_:
{
lean_object* v___x_2584_; 
v___x_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_a_2583_);
v___y_2564_ = v___y_2581_;
v___y_2565_ = v___y_2582_;
v_a_2566_ = v___x_2584_;
goto v___jp_2563_;
}
v___jp_2586_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___f_2593_; 
v___x_2588_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2292_, v___x_2585_, v___y_2587_);
v___x_2589_ = l_Lean_Elab_async;
v___x_2590_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2588_, v___x_2589_, v___x_2319_);
v___x_2591_ = lean_box_uint32(v_trustLevel_2295_);
v___x_2592_ = lean_box(v___x_2319_);
lean_inc(v_mainModuleName_2294_);
lean_inc_ref(v___x_2590_);
v___f_2593_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 10, 7);
lean_closure_set(v___f_2593_, 0, v_setup_x3f_2302_);
lean_closure_set(v___f_2593_, 1, v___f_2314_);
lean_closure_set(v___f_2593_, 2, v___x_2590_);
lean_closure_set(v___f_2593_, 3, v_plugins_2300_);
lean_closure_set(v___f_2593_, 4, v___x_2591_);
lean_closure_set(v___f_2593_, 5, v___x_2592_);
lean_closure_set(v___f_2593_, 6, v_mainModuleName_2294_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2304_) == 0)
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_box(0);
v___y_2564_ = v___f_2593_;
v___y_2565_ = v___x_2590_;
v_a_2566_ = v___x_2594_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2595_; lean_object* v___x_2596_; 
v_val_2595_ = lean_ctor_get(v_incrLoadFileName_x3f_2304_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2304_, 1);
v___x_2596_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2595_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v_snap_2598_; lean_object* v_initModIdxs_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v_snap_2598_ = lean_ctor_get(v_a_2597_, 0);
lean_inc_ref(v_snap_2598_);
v_initModIdxs_2599_ = lean_ctor_get(v_a_2597_, 1);
lean_inc_ref(v_initModIdxs_2599_);
lean_dec(v_a_2597_);
lean_inc(v_mainModuleName_2294_);
v___x_2600_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2598_, v_mainModuleName_2294_);
lean_inc_ref(v___x_2600_);
v___x_2601_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2600_);
v___x_2602_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2601_);
if (lean_obj_tag(v___x_2602_) == 1)
{
lean_object* v_val_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; 
v_val_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc(v_val_2603_);
lean_dec_ref_known(v___x_2602_, 1);
lean_inc_ref(v___x_2590_);
v___f_2604_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2604_, 0, v_val_2603_);
lean_closure_set(v___f_2604_, 1, v_initModIdxs_2599_);
lean_closure_set(v___f_2604_, 2, v___x_2590_);
v___x_2605_ = l_Lean_withImporting___redArg(v___f_2604_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v___x_2606_; 
lean_dec_ref_known(v___x_2605_, 1);
v___x_2606_ = lean_enable_initializer_execution();
v___y_2581_ = v___f_2593_;
v___y_2582_ = v___x_2590_;
v_a_2583_ = v___x_2600_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v___x_2600_);
lean_dec_ref(v___f_2593_);
lean_dec_ref(v___x_2590_);
lean_dec_ref(v___x_2383_);
lean_dec(v_incrHeaderSaveFileName_x3f_2305_);
lean_dec(v_incrSaveFileName_x3f_2303_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v_a_2607_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2605_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2605_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
else
{
lean_dec(v___x_2602_);
lean_dec_ref(v_initModIdxs_2599_);
v___y_2581_ = v___f_2593_;
v___y_2582_ = v___x_2590_;
v_a_2583_ = v___x_2600_;
goto v___jp_2580_;
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v___f_2593_);
lean_dec_ref(v___x_2590_);
lean_dec_ref(v___x_2383_);
lean_dec(v_incrHeaderSaveFileName_x3f_2305_);
lean_dec(v_incrSaveFileName_x3f_2303_);
lean_dec(v_oleanFileName_x3f_2296_);
lean_dec(v_mainModuleName_2294_);
v_a_2615_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2596_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2596_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2624_, lean_object* v_opts_2625_, lean_object* v_fileName_2626_, lean_object* v_mainModuleName_2627_, lean_object* v_trustLevel_2628_, lean_object* v_oleanFileName_x3f_2629_, lean_object* v_ileanFileName_x3f_2630_, lean_object* v_jsonOutput_2631_, lean_object* v_errorOnKinds_2632_, lean_object* v_plugins_2633_, lean_object* v_printStats_2634_, lean_object* v_setup_x3f_2635_, lean_object* v_incrSaveFileName_x3f_2636_, lean_object* v_incrLoadFileName_x3f_2637_, lean_object* v_incrHeaderSaveFileName_x3f_2638_, lean_object* v_a_2639_){
_start:
{
uint32_t v_trustLevel_boxed_2640_; uint8_t v_jsonOutput_boxed_2641_; uint8_t v_printStats_boxed_2642_; lean_object* v_res_2643_; 
v_trustLevel_boxed_2640_ = lean_unbox_uint32(v_trustLevel_2628_);
lean_dec(v_trustLevel_2628_);
v_jsonOutput_boxed_2641_ = lean_unbox(v_jsonOutput_2631_);
v_printStats_boxed_2642_ = lean_unbox(v_printStats_2634_);
v_res_2643_ = l_Lean_Elab_runFrontend(v_input_2624_, v_opts_2625_, v_fileName_2626_, v_mainModuleName_2627_, v_trustLevel_boxed_2640_, v_oleanFileName_x3f_2629_, v_ileanFileName_x3f_2630_, v_jsonOutput_boxed_2641_, v_errorOnKinds_2632_, v_plugins_2633_, v_printStats_boxed_2642_, v_setup_x3f_2635_, v_incrSaveFileName_x3f_2636_, v_incrLoadFileName_x3f_2637_, v_incrHeaderSaveFileName_x3f_2638_);
lean_dec_ref(v_errorOnKinds_2632_);
lean_dec(v_ileanFileName_x3f_2630_);
return v_res_2643_;
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
