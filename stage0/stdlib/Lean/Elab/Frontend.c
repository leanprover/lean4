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
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseCommand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_profileit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_getRegularInitAttrModIdxs(lean_object*);
lean_object* lean_compacted_region_save(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_runtime_forget(lean_object*);
lean_object* l_Lean_Language_SnapshotTask_get___redArg(lean_object*);
lean_object* l_IO_CancelToken_set(lean_object*);
lean_object* l_Lean_instFromJsonModuleArtifacts_fromJson(lean_object*);
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
lean_object* l_Lean_Linter_recordLints(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_postponeCompile;
lean_object* l_Lean_writeModule(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_LeanOptions_toOptions(lean_object*);
lean_object* l_Lean_Options_mergeBy(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_HeaderSyntax_isModule(lean_object*);
uint8_t lean_strict_or(uint8_t, uint8_t);
lean_object* l_Lean_Elab_HeaderSyntax_imports(lean_object*, uint8_t);
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
extern lean_object* l_Lean_Linter_codeQualityLogExt;
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_runAndReport(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Language_Lean_waitForFinalCmdState_x3f(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Elab_runFrontend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__0 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__0_value;
static const lean_closure_object l_Lean_Elab_runFrontend___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_runFrontend___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_runFrontend___closed__1 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__1_value;
static lean_once_cell_t l_Lean_Elab_runFrontend___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_runFrontend___closed__2;
static const lean_string_object l_Lean_Elab_runFrontend___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ".olean serialization"};
static const lean_object* l_Lean_Elab_runFrontend___closed__3 = (const lean_object*)&l_Lean_Elab_runFrontend___closed__3_value;
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
lean_object* v___x_11_; lean_object* v___x_13_; 
v___x_11_ = lean_box(0);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 0, v_commandState_1_);
v___x_13_ = v___x_9_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_commandState_1_);
lean_ctor_set(v_reuseFailAlloc_16_, 1, v_parserState_5_);
lean_ctor_set(v_reuseFailAlloc_16_, 2, v_cmdPos_6_);
lean_ctor_set(v_reuseFailAlloc_16_, 3, v_commands_7_);
v___x_13_ = v_reuseFailAlloc_16_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_st_ref_put(v_a_2_, v___x_13_);
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_11_);
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
lean_object* v___x_38_; lean_object* v_fileName_39_; lean_object* v_fileMap_40_; lean_object* v_commandState_41_; lean_object* v_cmdPos_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_38_ = lean_st_ref_get(v_a_36_);
v_fileName_39_ = lean_ctor_get(v_a_35_, 1);
v_fileMap_40_ = lean_ctor_get(v_a_35_, 2);
v_commandState_41_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_commandState_41_);
v_cmdPos_42_ = lean_ctor_get(v___x_38_, 2);
lean_inc(v_cmdPos_42_);
lean_dec(v___x_38_);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_box(0);
v___x_45_ = lean_box(0);
v___x_46_ = l_Lean_firstFrontendMacroScope;
v___x_47_ = lean_box(0);
v___x_48_ = 0;
lean_inc_ref(v_fileMap_40_);
lean_inc_ref(v_fileName_39_);
v___x_49_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_49_, 0, v_fileName_39_);
lean_ctor_set(v___x_49_, 1, v_fileMap_40_);
lean_ctor_set(v___x_49_, 2, v___x_43_);
lean_ctor_set(v___x_49_, 3, v_cmdPos_42_);
lean_ctor_set(v___x_49_, 4, v___x_44_);
lean_ctor_set(v___x_49_, 5, v___x_45_);
lean_ctor_set(v___x_49_, 6, v___x_46_);
lean_ctor_set(v___x_49_, 7, v___x_47_);
lean_ctor_set(v___x_49_, 8, v___x_45_);
lean_ctor_set(v___x_49_, 9, v___x_45_);
lean_ctor_set_uint8(v___x_49_, sizeof(void*)*10, v___x_48_);
v___x_50_ = lean_st_mk_ref(v_commandState_41_);
lean_inc(v___x_50_);
v___x_51_ = lean_apply_3(v_x_34_, v___x_49_, v___x_50_, lean_box(0));
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v___x_51_, 1);
v___x_53_ = lean_st_ref_get(v___x_50_);
lean_dec(v___x_50_);
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
lean_dec(v___x_50_);
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
lean_object* v___x_86_; lean_object* v_fileName_87_; lean_object* v_fileMap_88_; lean_object* v_commandState_89_; lean_object* v_cmdPos_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_86_ = lean_st_ref_get(v_a_84_);
v_fileName_87_ = lean_ctor_get(v_a_83_, 1);
v_fileMap_88_ = lean_ctor_get(v_a_83_, 2);
v_commandState_89_ = lean_ctor_get(v___x_86_, 0);
lean_inc_ref(v_commandState_89_);
v_cmdPos_90_ = lean_ctor_get(v___x_86_, 2);
lean_inc(v_cmdPos_90_);
lean_dec(v___x_86_);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_box(0);
v___x_93_ = lean_box(0);
v___x_94_ = l_Lean_firstFrontendMacroScope;
v___x_95_ = lean_box(0);
v___x_96_ = 0;
lean_inc_ref(v_fileMap_88_);
lean_inc_ref(v_fileName_87_);
v___x_97_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_97_, 0, v_fileName_87_);
lean_ctor_set(v___x_97_, 1, v_fileMap_88_);
lean_ctor_set(v___x_97_, 2, v___x_91_);
lean_ctor_set(v___x_97_, 3, v_cmdPos_90_);
lean_ctor_set(v___x_97_, 4, v___x_92_);
lean_ctor_set(v___x_97_, 5, v___x_93_);
lean_ctor_set(v___x_97_, 6, v___x_94_);
lean_ctor_set(v___x_97_, 7, v___x_95_);
lean_ctor_set(v___x_97_, 8, v___x_93_);
lean_ctor_set(v___x_97_, 9, v___x_93_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*10, v___x_96_);
v___x_98_ = lean_st_mk_ref(v_commandState_89_);
lean_inc(v___x_98_);
v___x_99_ = lean_apply_3(v_x_82_, v___x_97_, v___x_98_, lean_box(0));
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_99_, 1);
v___x_101_ = lean_st_ref_get(v___x_98_);
lean_dec(v___x_98_);
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
lean_dec(v___x_98_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend(lean_object* v_stx_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; lean_object* v_fileName_135_; lean_object* v_fileMap_136_; lean_object* v_commandState_137_; lean_object* v_cmdPos_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_134_ = lean_st_ref_get(v_a_132_);
v_fileName_135_ = lean_ctor_get(v_a_131_, 1);
v_fileMap_136_ = lean_ctor_get(v_a_131_, 2);
v_commandState_137_ = lean_ctor_get(v___x_134_, 0);
lean_inc_ref(v_commandState_137_);
v_cmdPos_138_ = lean_ctor_get(v___x_134_, 2);
lean_inc(v_cmdPos_138_);
lean_dec(v___x_134_);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_box(0);
v___x_141_ = lean_box(0);
v___x_142_ = l_Lean_firstFrontendMacroScope;
v___x_143_ = lean_box(0);
v___x_144_ = 0;
lean_inc_ref(v_fileMap_136_);
lean_inc_ref(v_fileName_135_);
v___x_145_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_145_, 0, v_fileName_135_);
lean_ctor_set(v___x_145_, 1, v_fileMap_136_);
lean_ctor_set(v___x_145_, 2, v___x_139_);
lean_ctor_set(v___x_145_, 3, v_cmdPos_138_);
lean_ctor_set(v___x_145_, 4, v___x_140_);
lean_ctor_set(v___x_145_, 5, v___x_141_);
lean_ctor_set(v___x_145_, 6, v___x_142_);
lean_ctor_set(v___x_145_, 7, v___x_143_);
lean_ctor_set(v___x_145_, 8, v___x_141_);
lean_ctor_set(v___x_145_, 9, v___x_141_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*10, v___x_144_);
v___x_146_ = lean_st_mk_ref(v_commandState_137_);
v___x_147_ = l_Lean_Elab_Command_elabCommandTopLevel(v_stx_130_, v___x_145_, v___x_146_);
lean_dec_ref_known(v___x_145_, 10);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_a_148_);
lean_dec_ref_known(v___x_147_, 1);
v___x_149_ = lean_st_ref_get(v___x_146_);
lean_dec(v___x_146_);
v___x_150_ = l_Lean_Elab_Frontend_setCommandState___redArg(v___x_149_, v_a_132_);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_150_, 0);
lean_dec(v_unused_158_);
v___x_152_ = v___x_150_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_dec(v___x_150_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v_a_148_);
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_148_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_171_; 
lean_dec(v___x_146_);
v_a_159_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_171_ == 0)
{
v___x_161_ = v___x_147_;
v_isShared_162_ = v_isSharedCheck_171_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_147_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_171_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_163_ = l_Lean_Exception_toMessageData(v_a_159_);
v___x_164_ = l_Lean_MessageData_toString(v___x_163_);
v___x_165_ = ((lean_object*)(l_Lean_Elab_Frontend_runCommandElabM___redArg___closed__0));
v___x_166_ = lean_string_append(v___x_165_, v___x_164_);
lean_dec_ref(v___x_164_);
v___x_167_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_167_);
v___x_169_ = v___x_161_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_elabCommandAtFrontend___boxed(lean_object* v_stx_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_stx_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg(lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_parserState_180_; lean_object* v_commandState_181_; lean_object* v_commands_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_193_; 
v___x_179_ = lean_st_ref_take(v_a_177_);
v_parserState_180_ = lean_ctor_get(v___x_179_, 1);
v_commandState_181_ = lean_ctor_get(v___x_179_, 0);
v_commands_182_ = lean_ctor_get(v___x_179_, 3);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v___x_179_, 2);
lean_dec(v_unused_194_);
v___x_184_ = v___x_179_;
v_isShared_185_ = v_isSharedCheck_193_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_commands_182_);
lean_inc(v_parserState_180_);
lean_inc(v_commandState_181_);
lean_dec(v___x_179_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_193_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v_pos_186_; lean_object* v___x_187_; lean_object* v___x_189_; 
v_pos_186_ = lean_ctor_get(v_parserState_180_, 0);
lean_inc(v_pos_186_);
v___x_187_ = lean_box(0);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 2, v_pos_186_);
v___x_189_ = v___x_184_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_commandState_181_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_parserState_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_pos_186_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_commands_182_);
v___x_189_ = v_reuseFailAlloc_192_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_st_ref_put(v_a_177_, v___x_189_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_187_);
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___redArg___boxed(lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_195_);
lean_dec(v_a_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos(lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_updateCmdPos___boxed(lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Elab_Frontend_updateCmdPos(v_a_202_, v_a_203_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg(lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_parserState_209_; lean_object* v___x_210_; 
v___x_208_ = lean_st_ref_get(v_a_206_);
v_parserState_209_ = lean_ctor_get(v___x_208_, 1);
lean_inc_ref(v_parserState_209_);
lean_dec(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_parserState_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___redArg___boxed(lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_211_);
lean_dec(v_a_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState(lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_215_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getParserState___boxed(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Frontend_getParserState(v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg(lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; lean_object* v_commandState_225_; lean_object* v___x_226_; 
v___x_224_ = lean_st_ref_get(v_a_222_);
v_commandState_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc_ref(v_commandState_225_);
lean_dec(v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_commandState_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___redArg___boxed(lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_227_);
lean_dec(v_a_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState(lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getCommandState___boxed(lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Elab_Frontend_getCommandState(v_a_234_, v_a_235_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg(lean_object* v_ps_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_241_; lean_object* v_commandState_242_; lean_object* v_cmdPos_243_; lean_object* v_commands_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_254_; 
v___x_241_ = lean_st_ref_take(v_a_239_);
v_commandState_242_ = lean_ctor_get(v___x_241_, 0);
v_cmdPos_243_ = lean_ctor_get(v___x_241_, 2);
v_commands_244_ = lean_ctor_get(v___x_241_, 3);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v___x_241_, 1);
lean_dec(v_unused_255_);
v___x_246_ = v___x_241_;
v_isShared_247_ = v_isSharedCheck_254_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_commands_244_);
lean_inc(v_cmdPos_243_);
lean_inc(v_commandState_242_);
lean_dec(v___x_241_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_254_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_248_ = lean_box(0);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_ps_238_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_commandState_242_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_ps_238_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v_cmdPos_243_);
lean_ctor_set(v_reuseFailAlloc_253_, 3, v_commands_244_);
v___x_250_ = v_reuseFailAlloc_253_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_st_ref_put(v_a_239_, v___x_250_);
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_248_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___redArg___boxed(lean_object* v_ps_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_256_, v_a_257_);
lean_dec(v_a_257_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState(lean_object* v_ps_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Elab_Frontend_setParserState___redArg(v_ps_260_, v_a_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setParserState___boxed(lean_object* v_ps_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Elab_Frontend_setParserState(v_ps_265_, v_a_266_, v_a_267_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg(lean_object* v_msgs_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; lean_object* v_commandState_274_; lean_object* v_parserState_275_; lean_object* v_cmdPos_276_; lean_object* v_commands_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_307_; 
v___x_273_ = lean_st_ref_take(v_a_271_);
v_commandState_274_ = lean_ctor_get(v___x_273_, 0);
v_parserState_275_ = lean_ctor_get(v___x_273_, 1);
v_cmdPos_276_ = lean_ctor_get(v___x_273_, 2);
v_commands_277_ = lean_ctor_get(v___x_273_, 3);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_307_ == 0)
{
v___x_279_ = v___x_273_;
v_isShared_280_ = v_isSharedCheck_307_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_commands_277_);
lean_inc(v_cmdPos_276_);
lean_inc(v_parserState_275_);
lean_inc(v_commandState_274_);
lean_dec(v___x_273_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_307_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v_env_281_; lean_object* v_scopes_282_; lean_object* v_usedQuotCtxts_283_; lean_object* v_nextMacroScope_284_; lean_object* v_maxRecDepth_285_; lean_object* v_ngen_286_; lean_object* v_auxDeclNGen_287_; lean_object* v_infoState_288_; lean_object* v_traceState_289_; lean_object* v_snapshotTasks_290_; lean_object* v_prevLinterStates_291_; lean_object* v_codeQualityEntryTasks_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_305_; 
v_env_281_ = lean_ctor_get(v_commandState_274_, 0);
v_scopes_282_ = lean_ctor_get(v_commandState_274_, 2);
v_usedQuotCtxts_283_ = lean_ctor_get(v_commandState_274_, 3);
v_nextMacroScope_284_ = lean_ctor_get(v_commandState_274_, 4);
v_maxRecDepth_285_ = lean_ctor_get(v_commandState_274_, 5);
v_ngen_286_ = lean_ctor_get(v_commandState_274_, 6);
v_auxDeclNGen_287_ = lean_ctor_get(v_commandState_274_, 7);
v_infoState_288_ = lean_ctor_get(v_commandState_274_, 8);
v_traceState_289_ = lean_ctor_get(v_commandState_274_, 9);
v_snapshotTasks_290_ = lean_ctor_get(v_commandState_274_, 10);
v_prevLinterStates_291_ = lean_ctor_get(v_commandState_274_, 11);
v_codeQualityEntryTasks_292_ = lean_ctor_get(v_commandState_274_, 12);
v_isSharedCheck_305_ = !lean_is_exclusive(v_commandState_274_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_commandState_274_, 1);
lean_dec(v_unused_306_);
v___x_294_ = v_commandState_274_;
v_isShared_295_ = v_isSharedCheck_305_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_codeQualityEntryTasks_292_);
lean_inc(v_prevLinterStates_291_);
lean_inc(v_snapshotTasks_290_);
lean_inc(v_traceState_289_);
lean_inc(v_infoState_288_);
lean_inc(v_auxDeclNGen_287_);
lean_inc(v_ngen_286_);
lean_inc(v_maxRecDepth_285_);
lean_inc(v_nextMacroScope_284_);
lean_inc(v_usedQuotCtxts_283_);
lean_inc(v_scopes_282_);
lean_inc(v_env_281_);
lean_dec(v_commandState_274_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_305_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_box(0);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 1, v_msgs_270_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_env_281_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_msgs_270_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_scopes_282_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_usedQuotCtxts_283_);
lean_ctor_set(v_reuseFailAlloc_304_, 4, v_nextMacroScope_284_);
lean_ctor_set(v_reuseFailAlloc_304_, 5, v_maxRecDepth_285_);
lean_ctor_set(v_reuseFailAlloc_304_, 6, v_ngen_286_);
lean_ctor_set(v_reuseFailAlloc_304_, 7, v_auxDeclNGen_287_);
lean_ctor_set(v_reuseFailAlloc_304_, 8, v_infoState_288_);
lean_ctor_set(v_reuseFailAlloc_304_, 9, v_traceState_289_);
lean_ctor_set(v_reuseFailAlloc_304_, 10, v_snapshotTasks_290_);
lean_ctor_set(v_reuseFailAlloc_304_, 11, v_prevLinterStates_291_);
lean_ctor_set(v_reuseFailAlloc_304_, 12, v_codeQualityEntryTasks_292_);
v___x_298_ = v_reuseFailAlloc_304_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_298_);
v___x_300_ = v___x_279_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_parserState_275_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_cmdPos_276_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_commands_277_);
v___x_300_ = v_reuseFailAlloc_303_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_st_ref_put(v_a_271_, v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_296_);
return v___x_302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* v_msgs_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_308_, v_a_309_);
lean_dec(v_a_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* v_msgs_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_312_, v_a_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* v_msgs_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Elab_Frontend_setMessages(v_msgs_317_, v_a_318_, v_a_319_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
lean_inc_ref(v_a_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v_a_322_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_325_);
lean_dec_ref(v_a_325_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc_ref(v_a_328_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_a_328_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Elab_Frontend_getInputContext(v_a_332_, v_a_333_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_336_, lean_object* v___x_337_, lean_object* v_a_338_, lean_object* v_messages_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
lean_inc_ref(v_a_336_);
v___x_341_ = l_Lean_Parser_parseCommand(v_a_336_, v___x_337_, v_a_338_, v_messages_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* v_a_342_, lean_object* v___x_343_, lean_object* v_a_344_, lean_object* v_messages_345_, lean_object* v_x_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Elab_Frontend_processCommand___lam__0(v_a_342_, v___x_343_, v_a_344_, v_messages_345_, v_x_346_);
lean_dec_ref(v_a_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_a_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v_env_358_; lean_object* v_messages_359_; lean_object* v_scopes_360_; lean_object* v___x_361_; lean_object* v_opts_362_; lean_object* v_currNamespace_363_; lean_object* v_openDecls_364_; lean_object* v___x_365_; lean_object* v___f_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_snd_370_; lean_object* v_fst_371_; lean_object* v_fst_372_; lean_object* v_snd_373_; lean_object* v___x_374_; lean_object* v_commandState_375_; lean_object* v_parserState_376_; lean_object* v_cmdPos_377_; lean_object* v_commands_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_408_; 
v___x_352_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_353_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_350_);
lean_dec_ref(v___x_353_);
v___x_354_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_350_);
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v___x_356_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_350_);
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
v___x_361_ = l_List_head_x21___redArg(v___x_352_, v_scopes_360_);
lean_dec(v_scopes_360_);
v_opts_362_ = lean_ctor_get(v___x_361_, 1);
lean_inc_ref_n(v_opts_362_, 2);
v_currNamespace_363_ = lean_ctor_get(v___x_361_, 2);
lean_inc(v_currNamespace_363_);
v_openDecls_364_ = lean_ctor_get(v___x_361_, 3);
lean_inc(v_openDecls_364_);
lean_dec(v___x_361_);
v___x_365_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_365_, 0, v_env_358_);
lean_ctor_set(v___x_365_, 1, v_opts_362_);
lean_ctor_set(v___x_365_, 2, v_currNamespace_363_);
lean_ctor_set(v___x_365_, 3, v_openDecls_364_);
lean_inc_ref(v_a_349_);
v___f_366_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_366_, 0, v_a_349_);
lean_closure_set(v___f_366_, 1, v___x_365_);
lean_closure_set(v___f_366_, 2, v_a_357_);
lean_closure_set(v___f_366_, 3, v_messages_359_);
v___x_367_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_368_ = lean_box(0);
v___x_369_ = lean_profileit(v___x_367_, v_opts_362_, v___f_366_, v___x_368_);
lean_dec_ref(v_opts_362_);
v_snd_370_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_snd_370_);
v_fst_371_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_fst_371_);
lean_dec(v___x_369_);
v_fst_372_ = lean_ctor_get(v_snd_370_, 0);
lean_inc(v_fst_372_);
v_snd_373_ = lean_ctor_get(v_snd_370_, 1);
lean_inc(v_snd_373_);
lean_dec(v_snd_370_);
v___x_374_ = lean_st_ref_take(v_a_350_);
v_commandState_375_ = lean_ctor_get(v___x_374_, 0);
v_parserState_376_ = lean_ctor_get(v___x_374_, 1);
v_cmdPos_377_ = lean_ctor_get(v___x_374_, 2);
v_commands_378_ = lean_ctor_get(v___x_374_, 3);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_408_ == 0)
{
v___x_380_ = v___x_374_;
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_commands_378_);
lean_inc(v_cmdPos_377_);
lean_inc(v_parserState_376_);
lean_inc(v_commandState_375_);
lean_dec(v___x_374_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_384_; 
lean_inc(v_fst_371_);
v___x_382_ = lean_array_push(v_commands_378_, v_fst_371_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 3, v___x_382_);
v___x_384_ = v___x_380_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_commandState_375_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_parserState_376_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_cmdPos_377_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v___x_382_);
v___x_384_ = v_reuseFailAlloc_407_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_385_ = lean_st_ref_put(v_a_350_, v___x_384_);
v___x_386_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_372_, v_a_350_);
lean_dec_ref(v___x_386_);
v___x_387_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_373_, v_a_350_);
lean_dec_ref(v___x_387_);
lean_inc(v_fst_371_);
v___x_388_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_371_, v_a_349_, v_a_350_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_397_; 
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_388_, 0);
lean_dec(v_unused_398_);
v___x_390_ = v___x_388_;
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
else
{
lean_dec(v___x_388_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_397_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_392_ = l_Lean_Parser_isTerminalCommand(v_fst_371_);
v___x_393_ = lean_box(v___x_392_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_393_);
v___x_395_ = v___x_390_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec(v_fst_371_);
v_a_399_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_388_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_388_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Elab_Frontend_processCommand(v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Elab_Frontend_processCommand(v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_427_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_427_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint8_t v___x_421_; 
v___x_421_ = lean_unbox(v_a_417_);
lean_dec(v_a_417_);
if (v___x_421_ == 0)
{
lean_del_object(v___x_419_);
goto _start;
}
else
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_box(0);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_423_);
v___x_425_ = v___x_419_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
v_a_428_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_416_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_416_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Elab_Frontend_processCommands(v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(lean_object* v_a_440_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_442_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_440_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_443_, size_t v_i_444_, size_t v_stop_445_, lean_object* v_b_446_){
_start:
{
lean_object* v___y_448_; uint8_t v___x_452_; 
v___x_452_ = lean_usize_dec_eq(v_i_444_, v_stop_445_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_array_uget_borrowed(v_as_443_, v_i_444_);
if (lean_obj_tag(v___x_453_) == 0)
{
v___y_448_ = v_b_446_;
goto v___jp_447_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_455_; 
v_val_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_val_454_);
v___x_455_ = lean_array_push(v_b_446_, v_val_454_);
v___y_448_ = v___x_455_;
goto v___jp_447_;
}
}
else
{
return v_b_446_;
}
v___jp_447_:
{
size_t v___x_449_; size_t v___x_450_; 
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_444_, v___x_449_);
v_i_444_ = v___x_450_;
v_b_446_ = v___y_448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_456_, lean_object* v_i_457_, lean_object* v_stop_458_, lean_object* v_b_459_){
_start:
{
size_t v_i_boxed_460_; size_t v_stop_boxed_461_; lean_object* v_res_462_; 
v_i_boxed_460_ = lean_unbox_usize(v_i_457_);
lean_dec(v_i_457_);
v_stop_boxed_461_ = lean_unbox_usize(v_stop_458_);
lean_dec(v_stop_458_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_456_, v_i_boxed_460_, v_stop_boxed_461_, v_b_459_);
lean_dec_ref(v_as_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_465_, lean_object* v_start_466_, lean_object* v_stop_467_){
_start:
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_469_ = lean_nat_dec_lt(v_start_466_, v_stop_467_);
if (v___x_469_ == 0)
{
return v___x_468_;
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_array_get_size(v_as_465_);
v___x_471_ = lean_nat_dec_le(v_stop_467_, v___x_470_);
if (v___x_471_ == 0)
{
uint8_t v___x_472_; 
v___x_472_ = lean_nat_dec_lt(v_start_466_, v___x_470_);
if (v___x_472_ == 0)
{
return v___x_468_;
}
else
{
size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v___x_473_ = lean_usize_of_nat(v_start_466_);
v___x_474_ = lean_usize_of_nat(v___x_470_);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_465_, v___x_473_, v___x_474_, v___x_468_);
return v___x_475_;
}
}
else
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_usize_of_nat(v_start_466_);
v___x_477_ = lean_usize_of_nat(v_stop_467_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_465_, v___x_476_, v___x_477_, v___x_468_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_479_, lean_object* v_start_480_, lean_object* v_stop_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_479_, v_start_480_, v_stop_481_);
lean_dec(v_stop_481_);
lean_dec(v_start_480_);
lean_dec_ref(v_as_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t v_sz_483_, size_t v_i_484_, lean_object* v_bs_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_484_, v_sz_483_);
if (v___x_486_ == 0)
{
return v_bs_485_;
}
else
{
lean_object* v_v_487_; lean_object* v_diagnostics_488_; lean_object* v_msgLog_489_; lean_object* v___x_490_; lean_object* v_bs_x27_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v_v_487_ = lean_array_uget_borrowed(v_bs_485_, v_i_484_);
v_diagnostics_488_ = lean_ctor_get(v_v_487_, 1);
v_msgLog_489_ = lean_ctor_get(v_diagnostics_488_, 0);
lean_inc_ref(v_msgLog_489_);
v___x_490_ = lean_unsigned_to_nat(0u);
v_bs_x27_491_ = lean_array_uset(v_bs_485_, v_i_484_, v___x_490_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_484_, v___x_492_);
v___x_494_ = lean_array_uset(v_bs_x27_491_, v_i_484_, v_msgLog_489_);
v_i_484_ = v___x_493_;
v_bs_485_ = v___x_494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_sz_496_, lean_object* v_i_497_, lean_object* v_bs_498_){
_start:
{
size_t v_sz_boxed_499_; size_t v_i_boxed_500_; lean_object* v_res_501_; 
v_sz_boxed_499_ = lean_unbox_usize(v_sz_496_);
lean_dec(v_sz_496_);
v_i_boxed_500_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_res_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_boxed_499_, v_i_boxed_500_, v_bs_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_502_, size_t v_i_503_, lean_object* v_bs_504_){
_start:
{
uint8_t v___x_505_; 
v___x_505_ = lean_usize_dec_lt(v_i_503_, v_sz_502_);
if (v___x_505_ == 0)
{
return v_bs_504_;
}
else
{
lean_object* v_v_506_; lean_object* v_elabSnap_507_; lean_object* v_infoTreeSnap_508_; lean_object* v___x_509_; lean_object* v_infoTree_x3f_510_; lean_object* v___x_511_; lean_object* v_bs_x27_512_; size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; 
v_v_506_ = lean_array_uget_borrowed(v_bs_504_, v_i_503_);
v_elabSnap_507_ = lean_ctor_get(v_v_506_, 3);
v_infoTreeSnap_508_ = lean_ctor_get(v_elabSnap_507_, 3);
lean_inc_ref(v_infoTreeSnap_508_);
v___x_509_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_508_);
v_infoTree_x3f_510_ = lean_ctor_get(v___x_509_, 2);
lean_inc(v_infoTree_x3f_510_);
lean_dec(v___x_509_);
v___x_511_ = lean_unsigned_to_nat(0u);
v_bs_x27_512_ = lean_array_uset(v_bs_504_, v_i_503_, v___x_511_);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_503_, v___x_513_);
v___x_515_ = lean_array_uset(v_bs_x27_512_, v_i_503_, v_infoTree_x3f_510_);
v_i_503_ = v___x_514_;
v_bs_504_ = v___x_515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_517_, lean_object* v_i_518_, lean_object* v_bs_519_){
_start:
{
size_t v_sz_boxed_520_; size_t v_i_boxed_521_; lean_object* v_res_522_; 
v_sz_boxed_520_ = lean_unbox_usize(v_sz_517_);
lean_dec(v_sz_517_);
v_i_boxed_521_ = lean_unbox_usize(v_i_518_);
lean_dec(v_i_518_);
v_res_522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_520_, v_i_boxed_521_, v_bs_519_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_523_, size_t v_i_524_, lean_object* v_bs_525_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = lean_usize_dec_lt(v_i_524_, v_sz_523_);
if (v___x_526_ == 0)
{
return v_bs_525_;
}
else
{
lean_object* v_v_527_; lean_object* v_stx_528_; lean_object* v___x_529_; lean_object* v_bs_x27_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v___x_533_; 
v_v_527_ = lean_array_uget_borrowed(v_bs_525_, v_i_524_);
v_stx_528_ = lean_ctor_get(v_v_527_, 1);
lean_inc(v_stx_528_);
v___x_529_ = lean_unsigned_to_nat(0u);
v_bs_x27_530_ = lean_array_uset(v_bs_525_, v_i_524_, v___x_529_);
v___x_531_ = ((size_t)1ULL);
v___x_532_ = lean_usize_add(v_i_524_, v___x_531_);
v___x_533_ = lean_array_uset(v_bs_x27_530_, v_i_524_, v_stx_528_);
v_i_524_ = v___x_532_;
v_bs_525_ = v___x_533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_535_, lean_object* v_i_536_, lean_object* v_bs_537_){
_start:
{
size_t v_sz_boxed_538_; size_t v_i_boxed_539_; lean_object* v_res_540_; 
v_sz_boxed_538_ = lean_unbox_usize(v_sz_535_);
lean_dec(v_sz_535_);
v_i_boxed_539_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_res_540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_538_, v_i_boxed_539_, v_bs_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object* v_as_541_, size_t v_i_542_, size_t v_stop_543_, lean_object* v_b_544_){
_start:
{
uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_eq(v_i_542_, v_stop_543_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; size_t v___x_548_; size_t v___x_549_; 
v___x_546_ = lean_array_uget_borrowed(v_as_541_, v_i_542_);
lean_inc(v___x_546_);
v___x_547_ = l_Lean_MessageLog_append(v_b_544_, v___x_546_);
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_i_542_, v___x_548_);
v_i_542_ = v___x_549_;
v_b_544_ = v___x_547_;
goto _start;
}
else
{
return v_b_544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object* v_as_551_, lean_object* v_i_552_, lean_object* v_stop_553_, lean_object* v_b_554_){
_start:
{
size_t v_i_boxed_555_; size_t v_stop_boxed_556_; lean_object* v_res_557_; 
v_i_boxed_555_ = lean_unbox_usize(v_i_552_);
lean_dec(v_i_552_);
v_stop_boxed_556_ = lean_unbox_usize(v_stop_553_);
lean_dec(v_stop_553_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v_as_551_, v_i_boxed_555_, v_stop_boxed_556_, v_b_554_);
lean_dec_ref(v_as_551_);
return v_res_557_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_unsigned_to_nat(32u);
v___x_559_ = lean_mk_empty_array_with_capacity(v___x_558_);
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_561_ = ((size_t)5ULL);
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = lean_unsigned_to_nat(32u);
v___x_564_ = lean_mk_empty_array_with_capacity(v___x_563_);
v___x_565_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_566_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_566_, 0, v___x_565_);
lean_ctor_set(v___x_566_, 1, v___x_564_);
lean_ctor_set(v___x_566_, 2, v___x_562_);
lean_ctor_set(v___x_566_, 3, v___x_562_);
lean_ctor_set_usize(v___x_566_, 4, v___x_561_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = l_Lean_NameSet_empty;
v___x_568_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
lean_ctor_set(v___x_569_, 2, v___x_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_570_, lean_object* v_initialSnap_571_, lean_object* v_t_572_, lean_object* v_commands_573_){
_start:
{
lean_object* v_snap_575_; lean_object* v_parserState_576_; lean_object* v_elabSnap_577_; lean_object* v_nextCmdSnap_x3f_578_; lean_object* v_commands_579_; 
v_snap_575_ = lean_task_get_own(v_t_572_);
v_parserState_576_ = lean_ctor_get(v_snap_575_, 2);
lean_inc_ref(v_parserState_576_);
v_elabSnap_577_ = lean_ctor_get(v_snap_575_, 3);
lean_inc_ref(v_elabSnap_577_);
v_nextCmdSnap_x3f_578_ = lean_ctor_get(v_snap_575_, 4);
lean_inc(v_nextCmdSnap_x3f_578_);
v_commands_579_ = lean_array_push(v_commands_573_, v_snap_575_);
if (lean_obj_tag(v_nextCmdSnap_x3f_578_) == 1)
{
lean_object* v_val_580_; lean_object* v_task_581_; 
lean_dec_ref(v_elabSnap_577_);
lean_dec_ref(v_parserState_576_);
v_val_580_ = lean_ctor_get(v_nextCmdSnap_x3f_578_, 0);
lean_inc(v_val_580_);
lean_dec_ref_known(v_nextCmdSnap_x3f_578_, 1);
v_task_581_ = lean_ctor_get(v_val_580_, 3);
lean_inc_ref(v_task_581_);
lean_dec(v_val_580_);
v_t_572_ = v_task_581_;
v_commands_573_ = v_commands_579_;
goto _start;
}
else
{
lean_object* v___x_583_; lean_object* v___y_585_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; size_t v_sz_641_; size_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
lean_dec(v_nextCmdSnap_x3f_578_);
v___x_583_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_571_);
v___x_639_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_initialSnap_571_);
v___x_640_ = l_Lean_Language_SnapshotTree_getAll(v___x_639_);
v_sz_641_ = lean_array_size(v___x_640_);
v___x_642_ = ((size_t)0ULL);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_641_, v___x_642_, v___x_640_);
v___x_644_ = lean_array_get_size(v___x_643_);
v___x_645_ = lean_nat_dec_lt(v___x_583_, v___x_644_);
if (v___x_645_ == 0)
{
lean_dec_ref(v___x_643_);
v___y_585_ = v___x_638_;
goto v___jp_584_;
}
else
{
uint8_t v___x_646_; 
v___x_646_ = lean_nat_dec_le(v___x_644_, v___x_644_);
if (v___x_646_ == 0)
{
if (v___x_645_ == 0)
{
lean_dec_ref(v___x_643_);
v___y_585_ = v___x_638_;
goto v___jp_584_;
}
else
{
size_t v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_usize_of_nat(v___x_644_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_643_, v___x_642_, v___x_647_, v___x_638_);
lean_dec_ref(v___x_643_);
v___y_585_ = v___x_648_;
goto v___jp_584_;
}
}
else
{
size_t v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_usize_of_nat(v___x_644_);
v___x_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_643_, v___x_642_, v___x_649_, v___x_638_);
lean_dec_ref(v___x_643_);
v___y_585_ = v___x_650_;
goto v___jp_584_;
}
}
v___jp_584_:
{
size_t v_sz_586_; lean_object* v_resultSnap_587_; lean_object* v___x_588_; lean_object* v_cmdState_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_635_; 
v_sz_586_ = lean_array_size(v_commands_579_);
v_resultSnap_587_ = lean_ctor_get(v_elabSnap_577_, 2);
lean_inc_ref(v_resultSnap_587_);
lean_dec_ref(v_elabSnap_577_);
v___x_588_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_587_);
v_cmdState_589_ = lean_ctor_get(v___x_588_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; lean_object* v_unused_637_; 
v_unused_636_ = lean_ctor_get(v___x_588_, 2);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_637_);
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_635_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_cmdState_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_635_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_infoState_593_; lean_object* v_env_594_; lean_object* v_scopes_595_; lean_object* v_usedQuotCtxts_596_; lean_object* v_nextMacroScope_597_; lean_object* v_maxRecDepth_598_; lean_object* v_ngen_599_; lean_object* v_auxDeclNGen_600_; lean_object* v_traceState_601_; lean_object* v_snapshotTasks_602_; lean_object* v_prevLinterStates_603_; lean_object* v_codeQualityEntryTasks_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_633_; 
v_infoState_593_ = lean_ctor_get(v_cmdState_589_, 8);
v_env_594_ = lean_ctor_get(v_cmdState_589_, 0);
v_scopes_595_ = lean_ctor_get(v_cmdState_589_, 2);
v_usedQuotCtxts_596_ = lean_ctor_get(v_cmdState_589_, 3);
v_nextMacroScope_597_ = lean_ctor_get(v_cmdState_589_, 4);
v_maxRecDepth_598_ = lean_ctor_get(v_cmdState_589_, 5);
v_ngen_599_ = lean_ctor_get(v_cmdState_589_, 6);
v_auxDeclNGen_600_ = lean_ctor_get(v_cmdState_589_, 7);
v_traceState_601_ = lean_ctor_get(v_cmdState_589_, 9);
v_snapshotTasks_602_ = lean_ctor_get(v_cmdState_589_, 10);
v_prevLinterStates_603_ = lean_ctor_get(v_cmdState_589_, 11);
v_codeQualityEntryTasks_604_ = lean_ctor_get(v_cmdState_589_, 12);
v_isSharedCheck_633_ = !lean_is_exclusive(v_cmdState_589_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_cmdState_589_, 1);
lean_dec(v_unused_634_);
v___x_606_ = v_cmdState_589_;
v_isShared_607_ = v_isSharedCheck_633_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_codeQualityEntryTasks_604_);
lean_inc(v_prevLinterStates_603_);
lean_inc(v_snapshotTasks_602_);
lean_inc(v_traceState_601_);
lean_inc(v_infoState_593_);
lean_inc(v_auxDeclNGen_600_);
lean_inc(v_ngen_599_);
lean_inc(v_maxRecDepth_598_);
lean_inc(v_nextMacroScope_597_);
lean_inc(v_usedQuotCtxts_596_);
lean_inc(v_scopes_595_);
lean_inc(v_env_594_);
lean_dec(v_cmdState_589_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_633_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
uint8_t v_enabled_608_; lean_object* v_assignment_609_; lean_object* v_lazyAssignment_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_631_; 
v_enabled_608_ = lean_ctor_get_uint8(v_infoState_593_, sizeof(void*)*3);
v_assignment_609_ = lean_ctor_get(v_infoState_593_, 0);
v_lazyAssignment_610_ = lean_ctor_get(v_infoState_593_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_infoState_593_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_infoState_593_, 2);
lean_dec(v_unused_632_);
v___x_612_ = v_infoState_593_;
v_isShared_613_ = v_isSharedCheck_631_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_lazyAssignment_610_);
lean_inc(v_assignment_609_);
lean_dec(v_infoState_593_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_631_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_pos_614_; size_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_trees_619_; lean_object* v___x_621_; 
v_pos_614_ = lean_ctor_get(v_parserState_576_, 0);
lean_inc(v_pos_614_);
v___x_615_ = ((size_t)0ULL);
lean_inc_ref(v_commands_579_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_586_, v___x_615_, v_commands_579_);
v___x_617_ = lean_array_get_size(v___x_616_);
v___x_618_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_616_, v___x_583_, v___x_617_);
lean_dec_ref(v___x_616_);
v_trees_619_ = l_Lean_Array_toPArray_x27___redArg(v___x_618_);
lean_dec_ref(v___x_618_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 2, v_trees_619_);
v___x_621_ = v___x_612_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_assignment_609_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_lazyAssignment_610_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_trees_619_);
lean_ctor_set_uint8(v_reuseFailAlloc_630_, sizeof(void*)*3, v_enabled_608_);
v___x_621_ = v_reuseFailAlloc_630_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 8, v___x_621_);
lean_ctor_set(v___x_606_, 1, v___y_585_);
v___x_623_ = v___x_606_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_env_594_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___y_585_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_scopes_595_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_usedQuotCtxts_596_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_nextMacroScope_597_);
lean_ctor_set(v_reuseFailAlloc_629_, 5, v_maxRecDepth_598_);
lean_ctor_set(v_reuseFailAlloc_629_, 6, v_ngen_599_);
lean_ctor_set(v_reuseFailAlloc_629_, 7, v_auxDeclNGen_600_);
lean_ctor_set(v_reuseFailAlloc_629_, 8, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_629_, 9, v_traceState_601_);
lean_ctor_set(v_reuseFailAlloc_629_, 10, v_snapshotTasks_602_);
lean_ctor_set(v_reuseFailAlloc_629_, 11, v_prevLinterStates_603_);
lean_ctor_set(v_reuseFailAlloc_629_, 12, v_codeQualityEntryTasks_604_);
v___x_623_ = v_reuseFailAlloc_629_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_586_, v___x_615_, v_commands_579_);
v___x_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v_parserState_576_);
lean_ctor_set(v___x_625_, 2, v_pos_614_);
lean_ctor_set(v___x_625_, 3, v___x_624_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 2, v_initialSnap_571_);
lean_ctor_set(v___x_591_, 1, v_inputCtx_570_);
lean_ctor_set(v___x_591_, 0, v___x_625_);
v___x_627_ = v___x_591_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_inputCtx_570_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_initialSnap_571_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_651_, lean_object* v_initialSnap_652_, lean_object* v_t_653_, lean_object* v_commands_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_651_, v_initialSnap_652_, v_t_653_, v_commands_654_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_659_, lean_object* v_parserState_660_, lean_object* v_commandState_661_, lean_object* v_old_x3f_662_){
_start:
{
lean_object* v___y_665_; 
if (lean_obj_tag(v_old_x3f_662_) == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_box(0);
v___y_665_ = v___x_670_;
goto v___jp_664_;
}
else
{
lean_object* v_val_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_681_; 
v_val_671_ = lean_ctor_get(v_old_x3f_662_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v_old_x3f_662_);
if (v_isSharedCheck_681_ == 0)
{
v___x_673_ = v_old_x3f_662_;
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_val_671_);
lean_dec(v_old_x3f_662_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_681_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_inputCtx_675_; lean_object* v_initialSnap_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v_inputCtx_675_ = lean_ctor_get(v_val_671_, 1);
lean_inc_ref(v_inputCtx_675_);
v_initialSnap_676_ = lean_ctor_get(v_val_671_, 2);
lean_inc_ref(v_initialSnap_676_);
lean_dec(v_val_671_);
v___x_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_677_, 0, v_inputCtx_675_);
lean_ctor_set(v___x_677_, 1, v_initialSnap_676_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_677_);
v___x_679_ = v___x_673_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
v___y_665_ = v___x_679_;
goto v___jp_664_;
}
}
}
v___jp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = l_Lean_Language_Lean_processCommands(v_inputCtx_659_, v_parserState_660_, v_commandState_661_, v___y_665_);
lean_inc_ref(v___x_666_);
v___x_667_ = lean_task_get_own(v___x_666_);
v___x_668_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_669_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_659_, v___x_667_, v___x_666_, v___x_668_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_682_, lean_object* v_parserState_683_, lean_object* v_commandState_684_, lean_object* v_old_x3f_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_682_, v_parserState_683_, v_commandState_684_, v_old_x3f_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_688_, lean_object* v_parserState_689_, lean_object* v_commandState_690_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_toState_694_; lean_object* v___x_695_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_688_, v_parserState_689_, v_commandState_690_, v___x_692_);
v_toState_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_toState_694_);
lean_dec_ref(v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v_toState_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_696_, lean_object* v_parserState_697_, lean_object* v_commandState_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Elab_IO_processCommands(v_inputCtx_696_, v_parserState_697_, v_commandState_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_706_, lean_object* v_env_707_, lean_object* v_opts_708_, lean_object* v_fileName_709_){
_start:
{
lean_object* v___y_712_; 
if (lean_obj_tag(v_fileName_709_) == 0)
{
lean_object* v___x_732_; 
v___x_732_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_712_ = v___x_732_;
goto v___jp_711_;
}
else
{
lean_object* v_val_733_; 
v_val_733_ = lean_ctor_get(v_fileName_709_, 0);
lean_inc(v_val_733_);
lean_dec_ref_known(v_fileName_709_, 1);
v___y_712_ = v_val_733_;
goto v___jp_711_;
}
v___jp_711_:
{
uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v_inputCtx_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_731_; 
v___x_713_ = 1;
v___x_714_ = lean_string_utf8_byte_size(v_input_706_);
v_inputCtx_715_ = l_Lean_Parser_mkInputContext___redArg(v_input_706_, v___y_712_, v___x_713_, v___x_714_);
v___x_716_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_717_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_718_ = l_Lean_Elab_Command_mkState(v_env_707_, v___x_717_, v_opts_708_);
v___x_719_ = l_Lean_Elab_IO_processCommands(v_inputCtx_715_, v___x_716_, v___x_718_);
v_a_720_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_731_ == 0)
{
v___x_722_ = v___x_719_;
v_isShared_723_ = v_isSharedCheck_731_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_731_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_commandState_724_; lean_object* v_env_725_; lean_object* v_messages_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v_commandState_724_ = lean_ctor_get(v_a_720_, 0);
lean_inc_ref(v_commandState_724_);
lean_dec(v_a_720_);
v_env_725_ = lean_ctor_get(v_commandState_724_, 0);
lean_inc_ref(v_env_725_);
v_messages_726_ = lean_ctor_get(v_commandState_724_, 1);
lean_inc_ref(v_messages_726_);
lean_dec_ref(v_commandState_724_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_env_725_);
lean_ctor_set(v___x_727_, 1, v_messages_726_);
if (v_isShared_723_ == 0)
{
lean_ctor_set(v___x_722_, 0, v___x_727_);
v___x_729_ = v___x_722_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_734_, lean_object* v_env_735_, lean_object* v_opts_736_, lean_object* v_fileName_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Elab_process(v_input_734_, v_env_735_, v_opts_736_, v_fileName_737_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_740_, lean_object* v_cmdStx_x3f_741_, lean_object* v_acc_742_){
_start:
{
lean_object* v_element_743_; lean_object* v_diagnostics_744_; lean_object* v_children_745_; lean_object* v_msgLog_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_764_; 
v_element_743_ = lean_ctor_get(v_t_740_, 0);
v_diagnostics_744_ = lean_ctor_get(v_element_743_, 1);
lean_inc_ref(v_diagnostics_744_);
v_children_745_ = lean_ctor_get(v_t_740_, 1);
lean_inc_ref(v_children_745_);
lean_dec_ref(v_t_740_);
v_msgLog_746_ = lean_ctor_get(v_diagnostics_744_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_diagnostics_744_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v_diagnostics_744_, 1);
lean_dec(v_unused_765_);
v___x_748_ = v_diagnostics_744_;
v_isShared_749_ = v_isSharedCheck_764_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_msgLog_746_);
lean_dec(v_diagnostics_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_764_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
lean_inc(v_cmdStx_x3f_741_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v_msgLog_746_);
lean_ctor_set(v___x_748_, 0, v_cmdStx_x3f_741_);
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_cmdStx_x3f_741_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_msgLog_746_);
v___x_751_ = v_reuseFailAlloc_763_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v_acc_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_acc_752_ = lean_array_push(v_acc_742_, v___x_751_);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_array_get_size(v_children_745_);
v___x_755_ = lean_nat_dec_lt(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec_ref(v_children_745_);
lean_dec(v_cmdStx_x3f_741_);
return v_acc_752_;
}
else
{
uint8_t v___x_756_; 
v___x_756_ = lean_nat_dec_le(v___x_754_, v___x_754_);
if (v___x_756_ == 0)
{
if (v___x_755_ == 0)
{
lean_dec_ref(v_children_745_);
lean_dec(v_cmdStx_x3f_741_);
return v_acc_752_;
}
else
{
size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((size_t)0ULL);
v___x_758_ = lean_usize_of_nat(v___x_754_);
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_741_, v_children_745_, v___x_757_, v___x_758_, v_acc_752_);
lean_dec_ref(v_children_745_);
return v___x_759_;
}
}
else
{
size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v___x_760_ = ((size_t)0ULL);
v___x_761_ = lean_usize_of_nat(v___x_754_);
v___x_762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_741_, v_children_745_, v___x_760_, v___x_761_, v_acc_752_);
lean_dec_ref(v_children_745_);
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_766_, lean_object* v_as_767_, size_t v_i_768_, size_t v_stop_769_, lean_object* v_b_770_){
_start:
{
lean_object* v___y_772_; uint8_t v___x_776_; 
v___x_776_ = lean_usize_dec_eq(v_i_768_, v_stop_769_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v_stx_x3f_778_; lean_object* v___x_779_; 
v___x_777_ = lean_array_uget_borrowed(v_as_767_, v_i_768_);
v_stx_x3f_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v___x_777_);
v___x_779_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_777_);
if (lean_obj_tag(v_stx_x3f_778_) == 0)
{
lean_object* v___x_780_; 
lean_inc(v_cmdStx_x3f_766_);
v___x_780_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_779_, v_cmdStx_x3f_766_, v_b_770_);
v___y_772_ = v___x_780_;
goto v___jp_771_;
}
else
{
lean_object* v___x_781_; 
lean_inc_ref(v_stx_x3f_778_);
v___x_781_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_779_, v_stx_x3f_778_, v_b_770_);
v___y_772_ = v___x_781_;
goto v___jp_771_;
}
}
else
{
lean_dec(v_cmdStx_x3f_766_);
return v_b_770_;
}
v___jp_771_:
{
size_t v___x_773_; size_t v___x_774_; 
v___x_773_ = ((size_t)1ULL);
v___x_774_ = lean_usize_add(v_i_768_, v___x_773_);
v_i_768_ = v___x_774_;
v_b_770_ = v___y_772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_782_, lean_object* v_as_783_, lean_object* v_i_784_, lean_object* v_stop_785_, lean_object* v_b_786_){
_start:
{
size_t v_i_boxed_787_; size_t v_stop_boxed_788_; lean_object* v_res_789_; 
v_i_boxed_787_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_stop_boxed_788_ = lean_unbox_usize(v_stop_785_);
lean_dec(v_stop_785_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_782_, v_as_783_, v_i_boxed_787_, v_stop_boxed_788_, v_b_786_);
lean_dec_ref(v_as_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_lean_x3f_792_; lean_object* v_olean_x3f_793_; lean_object* v_oleanServer_x3f_794_; lean_object* v_ilean_x3f_795_; lean_object* v_irSig_x3f_796_; lean_object* v_ir_x3f_797_; lean_object* v_c_x3f_798_; lean_object* v_bc_x3f_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_lean_x3f_792_ = lean_ctor_get(v_a_791_, 0);
v_olean_x3f_793_ = lean_ctor_get(v_a_791_, 1);
v_oleanServer_x3f_794_ = lean_ctor_get(v_a_791_, 2);
v_ilean_x3f_795_ = lean_ctor_get(v_a_791_, 4);
v_irSig_x3f_796_ = lean_ctor_get(v_a_791_, 5);
v_ir_x3f_797_ = lean_ctor_get(v_a_791_, 6);
v_c_x3f_798_ = lean_ctor_get(v_a_791_, 7);
v_bc_x3f_799_ = lean_ctor_get(v_a_791_, 8);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_791_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_a_791_, 3);
lean_dec(v_unused_808_);
v___x_801_ = v_a_791_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_bc_x3f_799_);
lean_inc(v_c_x3f_798_);
lean_inc(v_ir_x3f_797_);
lean_inc(v_irSig_x3f_796_);
lean_inc(v_ilean_x3f_795_);
lean_inc(v_oleanServer_x3f_794_);
lean_inc(v_olean_x3f_793_);
lean_inc(v_lean_x3f_792_);
lean_dec(v_a_791_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v_filePath_790_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 3, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_lean_x3f_792_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_olean_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_oleanServer_x3f_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_ilean_x3f_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 5, v_irSig_x3f_796_);
lean_ctor_set(v_reuseFailAlloc_806_, 6, v_ir_x3f_797_);
lean_ctor_set(v_reuseFailAlloc_806_, 7, v_c_x3f_798_);
lean_ctor_set(v_reuseFailAlloc_806_, 8, v_bc_x3f_799_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_lean_x3f_811_; lean_object* v_olean_x3f_812_; lean_object* v_oleanServer_x3f_813_; lean_object* v_oleanPrivate_x3f_814_; lean_object* v_ilean_x3f_815_; lean_object* v_ir_x3f_816_; lean_object* v_c_x3f_817_; lean_object* v_bc_x3f_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_826_; 
v_lean_x3f_811_ = lean_ctor_get(v_a_810_, 0);
v_olean_x3f_812_ = lean_ctor_get(v_a_810_, 1);
v_oleanServer_x3f_813_ = lean_ctor_get(v_a_810_, 2);
v_oleanPrivate_x3f_814_ = lean_ctor_get(v_a_810_, 3);
v_ilean_x3f_815_ = lean_ctor_get(v_a_810_, 4);
v_ir_x3f_816_ = lean_ctor_get(v_a_810_, 6);
v_c_x3f_817_ = lean_ctor_get(v_a_810_, 7);
v_bc_x3f_818_ = lean_ctor_get(v_a_810_, 8);
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_a_810_, 5);
lean_dec(v_unused_827_);
v___x_820_ = v_a_810_;
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_bc_x3f_818_);
lean_inc(v_c_x3f_817_);
lean_inc(v_ir_x3f_816_);
lean_inc(v_ilean_x3f_815_);
lean_inc(v_oleanPrivate_x3f_814_);
lean_inc(v_oleanServer_x3f_813_);
lean_inc(v_olean_x3f_812_);
lean_inc(v_lean_x3f_811_);
lean_dec(v_a_810_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_826_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_filePath_809_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 5, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_lean_x3f_811_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v_olean_x3f_812_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_oleanServer_x3f_813_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_oleanPrivate_x3f_814_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v_ilean_x3f_815_);
lean_ctor_set(v_reuseFailAlloc_825_, 5, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_825_, 6, v_ir_x3f_816_);
lean_ctor_set(v_reuseFailAlloc_825_, 7, v_c_x3f_817_);
lean_ctor_set(v_reuseFailAlloc_825_, 8, v_bc_x3f_818_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_lean_x3f_830_; lean_object* v_olean_x3f_831_; lean_object* v_oleanPrivate_x3f_832_; lean_object* v_ilean_x3f_833_; lean_object* v_irSig_x3f_834_; lean_object* v_ir_x3f_835_; lean_object* v_c_x3f_836_; lean_object* v_bc_x3f_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_845_; 
v_lean_x3f_830_ = lean_ctor_get(v_a_829_, 0);
v_olean_x3f_831_ = lean_ctor_get(v_a_829_, 1);
v_oleanPrivate_x3f_832_ = lean_ctor_get(v_a_829_, 3);
v_ilean_x3f_833_ = lean_ctor_get(v_a_829_, 4);
v_irSig_x3f_834_ = lean_ctor_get(v_a_829_, 5);
v_ir_x3f_835_ = lean_ctor_get(v_a_829_, 6);
v_c_x3f_836_ = lean_ctor_get(v_a_829_, 7);
v_bc_x3f_837_ = lean_ctor_get(v_a_829_, 8);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_829_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_a_829_, 2);
lean_dec(v_unused_846_);
v___x_839_ = v_a_829_;
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_bc_x3f_837_);
lean_inc(v_c_x3f_836_);
lean_inc(v_ir_x3f_835_);
lean_inc(v_irSig_x3f_834_);
lean_inc(v_ilean_x3f_833_);
lean_inc(v_oleanPrivate_x3f_832_);
lean_inc(v_olean_x3f_831_);
lean_inc(v_lean_x3f_830_);
lean_dec(v_a_829_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_845_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_841_, 0, v_filePath_828_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 2, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_lean_x3f_830_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_olean_x3f_831_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 3, v_oleanPrivate_x3f_832_);
lean_ctor_set(v_reuseFailAlloc_844_, 4, v_ilean_x3f_833_);
lean_ctor_set(v_reuseFailAlloc_844_, 5, v_irSig_x3f_834_);
lean_ctor_set(v_reuseFailAlloc_844_, 6, v_ir_x3f_835_);
lean_ctor_set(v_reuseFailAlloc_844_, 7, v_c_x3f_836_);
lean_ctor_set(v_reuseFailAlloc_844_, 8, v_bc_x3f_837_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_847_, lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
uint8_t v___x_849_; 
v___x_849_ = 0;
return v___x_849_;
}
else
{
lean_object* v_key_850_; lean_object* v_tail_851_; uint8_t v___x_852_; 
v_key_850_ = lean_ctor_get(v_x_848_, 0);
v_tail_851_ = lean_ctor_get(v_x_848_, 2);
v___x_852_ = lean_string_dec_eq(v_key_850_, v_a_847_);
if (v___x_852_ == 0)
{
v_x_848_ = v_tail_851_;
goto _start;
}
else
{
return v___x_852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_854_, lean_object* v_x_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_854_, v_x_855_);
lean_dec(v_x_855_);
lean_dec_ref(v_a_854_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_buckets_860_; lean_object* v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; uint64_t v___x_864_; uint64_t v_fold_865_; uint64_t v___x_866_; uint64_t v___x_867_; uint64_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_buckets_860_ = lean_ctor_get(v_m_858_, 1);
v___x_861_ = lean_array_get_size(v_buckets_860_);
v___x_862_ = lean_string_hash(v_a_859_);
v___x_863_ = 32ULL;
v___x_864_ = lean_uint64_shift_right(v___x_862_, v___x_863_);
v_fold_865_ = lean_uint64_xor(v___x_862_, v___x_864_);
v___x_866_ = 16ULL;
v___x_867_ = lean_uint64_shift_right(v_fold_865_, v___x_866_);
v___x_868_ = lean_uint64_xor(v_fold_865_, v___x_867_);
v___x_869_ = lean_uint64_to_usize(v___x_868_);
v___x_870_ = lean_usize_of_nat(v___x_861_);
v___x_871_ = ((size_t)1ULL);
v___x_872_ = lean_usize_sub(v___x_870_, v___x_871_);
v___x_873_ = lean_usize_land(v___x_869_, v___x_872_);
v___x_874_ = lean_array_uget_borrowed(v_buckets_860_, v___x_873_);
v___x_875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_859_, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_876_, lean_object* v_a_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_876_, v_a_877_);
lean_dec_ref(v_a_877_);
lean_dec_ref(v_m_876_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_880_, lean_object* v_fallback_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_inc(v_fallback_881_);
return v_fallback_881_;
}
else
{
lean_object* v_key_883_; lean_object* v_value_884_; lean_object* v_tail_885_; uint8_t v___x_886_; 
v_key_883_ = lean_ctor_get(v_x_882_, 0);
v_value_884_ = lean_ctor_get(v_x_882_, 1);
v_tail_885_ = lean_ctor_get(v_x_882_, 2);
v___x_886_ = lean_string_dec_eq(v_key_883_, v_a_880_);
if (v___x_886_ == 0)
{
v_x_882_ = v_tail_885_;
goto _start;
}
else
{
lean_inc(v_value_884_);
return v_value_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_888_, lean_object* v_fallback_889_, lean_object* v_x_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_888_, v_fallback_889_, v_x_890_);
lean_dec(v_x_890_);
lean_dec(v_fallback_889_);
lean_dec_ref(v_a_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_892_, lean_object* v_a_893_, lean_object* v_fallback_894_){
_start:
{
lean_object* v_buckets_895_; lean_object* v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; uint64_t v_fold_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; size_t v___x_904_; size_t v___x_905_; size_t v___x_906_; size_t v___x_907_; size_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_buckets_895_ = lean_ctor_get(v_m_892_, 1);
v___x_896_ = lean_array_get_size(v_buckets_895_);
v___x_897_ = lean_string_hash(v_a_893_);
v___x_898_ = 32ULL;
v___x_899_ = lean_uint64_shift_right(v___x_897_, v___x_898_);
v_fold_900_ = lean_uint64_xor(v___x_897_, v___x_899_);
v___x_901_ = 16ULL;
v___x_902_ = lean_uint64_shift_right(v_fold_900_, v___x_901_);
v___x_903_ = lean_uint64_xor(v_fold_900_, v___x_902_);
v___x_904_ = lean_uint64_to_usize(v___x_903_);
v___x_905_ = lean_usize_of_nat(v___x_896_);
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_sub(v___x_905_, v___x_906_);
v___x_908_ = lean_usize_land(v___x_904_, v___x_907_);
v___x_909_ = lean_array_uget_borrowed(v_buckets_895_, v___x_908_);
v___x_910_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_893_, v_fallback_894_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_911_, lean_object* v_a_912_, lean_object* v_fallback_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_911_, v_a_912_, v_fallback_913_);
lean_dec(v_fallback_913_);
lean_dec_ref(v_a_912_);
lean_dec_ref(v_m_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_lean_x3f_917_; lean_object* v_olean_x3f_918_; lean_object* v_oleanServer_x3f_919_; lean_object* v_oleanPrivate_x3f_920_; lean_object* v_ilean_x3f_921_; lean_object* v_irSig_x3f_922_; lean_object* v_c_x3f_923_; lean_object* v_bc_x3f_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
v_lean_x3f_917_ = lean_ctor_get(v_a_916_, 0);
v_olean_x3f_918_ = lean_ctor_get(v_a_916_, 1);
v_oleanServer_x3f_919_ = lean_ctor_get(v_a_916_, 2);
v_oleanPrivate_x3f_920_ = lean_ctor_get(v_a_916_, 3);
v_ilean_x3f_921_ = lean_ctor_get(v_a_916_, 4);
v_irSig_x3f_922_ = lean_ctor_get(v_a_916_, 5);
v_c_x3f_923_ = lean_ctor_get(v_a_916_, 7);
v_bc_x3f_924_ = lean_ctor_get(v_a_916_, 8);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_916_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_a_916_, 6);
lean_dec(v_unused_933_);
v___x_926_ = v_a_916_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_bc_x3f_924_);
lean_inc(v_c_x3f_923_);
lean_inc(v_irSig_x3f_922_);
lean_inc(v_ilean_x3f_921_);
lean_inc(v_oleanPrivate_x3f_920_);
lean_inc(v_oleanServer_x3f_919_);
lean_inc(v_olean_x3f_918_);
lean_inc(v_lean_x3f_917_);
lean_dec(v_a_916_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_928_, 0, v_filePath_915_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 6, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_lean_x3f_917_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_olean_x3f_918_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_oleanServer_x3f_919_);
lean_ctor_set(v_reuseFailAlloc_931_, 3, v_oleanPrivate_x3f_920_);
lean_ctor_set(v_reuseFailAlloc_931_, 4, v_ilean_x3f_921_);
lean_ctor_set(v_reuseFailAlloc_931_, 5, v_irSig_x3f_922_);
lean_ctor_set(v_reuseFailAlloc_931_, 6, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 7, v_c_x3f_923_);
lean_ctor_set(v_reuseFailAlloc_931_, 8, v_bc_x3f_924_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_lean_x3f_936_; lean_object* v_oleanServer_x3f_937_; lean_object* v_oleanPrivate_x3f_938_; lean_object* v_ilean_x3f_939_; lean_object* v_irSig_x3f_940_; lean_object* v_ir_x3f_941_; lean_object* v_c_x3f_942_; lean_object* v_bc_x3f_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v_lean_x3f_936_ = lean_ctor_get(v_a_935_, 0);
v_oleanServer_x3f_937_ = lean_ctor_get(v_a_935_, 2);
v_oleanPrivate_x3f_938_ = lean_ctor_get(v_a_935_, 3);
v_ilean_x3f_939_ = lean_ctor_get(v_a_935_, 4);
v_irSig_x3f_940_ = lean_ctor_get(v_a_935_, 5);
v_ir_x3f_941_ = lean_ctor_get(v_a_935_, 6);
v_c_x3f_942_ = lean_ctor_get(v_a_935_, 7);
v_bc_x3f_943_ = lean_ctor_get(v_a_935_, 8);
v_isSharedCheck_951_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v_a_935_, 1);
lean_dec(v_unused_952_);
v___x_945_ = v_a_935_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_bc_x3f_943_);
lean_inc(v_c_x3f_942_);
lean_inc(v_ir_x3f_941_);
lean_inc(v_irSig_x3f_940_);
lean_inc(v_ilean_x3f_939_);
lean_inc(v_oleanPrivate_x3f_938_);
lean_inc(v_oleanServer_x3f_937_);
lean_inc(v_lean_x3f_936_);
lean_dec(v_a_935_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_947_, 0, v_filePath_934_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_lean_x3f_936_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_oleanServer_x3f_937_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_oleanPrivate_x3f_938_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_ilean_x3f_939_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v_irSig_x3f_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_ir_x3f_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_c_x3f_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v_bc_x3f_943_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_953_, lean_object* v_b_954_, lean_object* v_x_955_){
_start:
{
if (lean_obj_tag(v_x_955_) == 0)
{
lean_dec(v_b_954_);
lean_dec_ref(v_a_953_);
return v_x_955_;
}
else
{
lean_object* v_key_956_; lean_object* v_value_957_; lean_object* v_tail_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_970_; 
v_key_956_ = lean_ctor_get(v_x_955_, 0);
v_value_957_ = lean_ctor_get(v_x_955_, 1);
v_tail_958_ = lean_ctor_get(v_x_955_, 2);
v_isSharedCheck_970_ = !lean_is_exclusive(v_x_955_);
if (v_isSharedCheck_970_ == 0)
{
v___x_960_ = v_x_955_;
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_tail_958_);
lean_inc(v_value_957_);
lean_inc(v_key_956_);
lean_dec(v_x_955_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
uint8_t v___x_962_; 
v___x_962_ = lean_string_dec_eq(v_key_956_, v_a_953_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_953_, v_b_954_, v_tail_958_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 2, v___x_963_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_key_956_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_value_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
else
{
lean_object* v___x_968_; 
lean_dec(v_value_957_);
lean_dec(v_key_956_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_b_954_);
lean_ctor_set(v___x_960_, 0, v_a_953_);
v___x_968_ = v___x_960_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_953_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_b_954_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_tail_958_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_972_) == 0)
{
return v_x_971_;
}
else
{
lean_object* v_key_973_; lean_object* v_value_974_; lean_object* v_tail_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_998_; 
v_key_973_ = lean_ctor_get(v_x_972_, 0);
v_value_974_ = lean_ctor_get(v_x_972_, 1);
v_tail_975_ = lean_ctor_get(v_x_972_, 2);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_972_);
if (v_isSharedCheck_998_ == 0)
{
v___x_977_ = v_x_972_;
v_isShared_978_ = v_isSharedCheck_998_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_tail_975_);
lean_inc(v_value_974_);
lean_inc(v_key_973_);
lean_dec(v_x_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_998_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; uint64_t v___x_980_; uint64_t v___x_981_; uint64_t v___x_982_; uint64_t v_fold_983_; uint64_t v___x_984_; uint64_t v___x_985_; uint64_t v___x_986_; size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_979_ = lean_array_get_size(v_x_971_);
v___x_980_ = lean_string_hash(v_key_973_);
v___x_981_ = 32ULL;
v___x_982_ = lean_uint64_shift_right(v___x_980_, v___x_981_);
v_fold_983_ = lean_uint64_xor(v___x_980_, v___x_982_);
v___x_984_ = 16ULL;
v___x_985_ = lean_uint64_shift_right(v_fold_983_, v___x_984_);
v___x_986_ = lean_uint64_xor(v_fold_983_, v___x_985_);
v___x_987_ = lean_uint64_to_usize(v___x_986_);
v___x_988_ = lean_usize_of_nat(v___x_979_);
v___x_989_ = ((size_t)1ULL);
v___x_990_ = lean_usize_sub(v___x_988_, v___x_989_);
v___x_991_ = lean_usize_land(v___x_987_, v___x_990_);
v___x_992_ = lean_array_uget_borrowed(v_x_971_, v___x_991_);
lean_inc(v___x_992_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 2, v___x_992_);
v___x_994_ = v___x_977_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_key_973_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_value_974_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v___x_992_);
v___x_994_ = v_reuseFailAlloc_997_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; 
v___x_995_ = lean_array_uset(v_x_971_, v___x_991_, v___x_994_);
v_x_971_ = v___x_995_;
v_x_972_ = v_tail_975_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_999_, lean_object* v_source_1000_, lean_object* v_target_1001_){
_start:
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_array_get_size(v_source_1000_);
v___x_1003_ = lean_nat_dec_lt(v_i_999_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_dec_ref(v_source_1000_);
lean_dec(v_i_999_);
return v_target_1001_;
}
else
{
lean_object* v_es_1004_; lean_object* v___x_1005_; lean_object* v_source_1006_; lean_object* v_target_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_es_1004_ = lean_array_fget(v_source_1000_, v_i_999_);
v___x_1005_ = lean_box(0);
v_source_1006_ = lean_array_fset(v_source_1000_, v_i_999_, v___x_1005_);
v_target_1007_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_1001_, v_es_1004_);
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_i_999_, v___x_1008_);
lean_dec(v_i_999_);
v_i_999_ = v___x_1009_;
v_source_1000_ = v_source_1006_;
v_target_1001_ = v_target_1007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_1011_){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_nbuckets_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1012_ = lean_array_get_size(v_data_1011_);
v___x_1013_ = lean_unsigned_to_nat(2u);
v_nbuckets_1014_ = lean_nat_mul(v___x_1012_, v___x_1013_);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_box(0);
v___x_1017_ = lean_mk_array(v_nbuckets_1014_, v___x_1016_);
v___x_1018_ = lean_array_propagate_mark(v_data_1011_, v___x_1017_);
v___x_1019_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1015_, v_data_1011_, v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1020_, lean_object* v_a_1021_, lean_object* v_b_1022_){
_start:
{
lean_object* v_size_1023_; lean_object* v_buckets_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1067_; 
v_size_1023_ = lean_ctor_get(v_m_1020_, 0);
v_buckets_1024_ = lean_ctor_get(v_m_1020_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_m_1020_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1026_ = v_m_1020_;
v_isShared_1027_ = v_isSharedCheck_1067_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_buckets_1024_);
lean_inc(v_size_1023_);
lean_dec(v_m_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1067_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; uint64_t v___x_1031_; uint64_t v_fold_1032_; uint64_t v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v_bkt_1041_; uint8_t v___x_1042_; 
v___x_1028_ = lean_array_get_size(v_buckets_1024_);
v___x_1029_ = lean_string_hash(v_a_1021_);
v___x_1030_ = 32ULL;
v___x_1031_ = lean_uint64_shift_right(v___x_1029_, v___x_1030_);
v_fold_1032_ = lean_uint64_xor(v___x_1029_, v___x_1031_);
v___x_1033_ = 16ULL;
v___x_1034_ = lean_uint64_shift_right(v_fold_1032_, v___x_1033_);
v___x_1035_ = lean_uint64_xor(v_fold_1032_, v___x_1034_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = lean_usize_of_nat(v___x_1028_);
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_sub(v___x_1037_, v___x_1038_);
v___x_1040_ = lean_usize_land(v___x_1036_, v___x_1039_);
v_bkt_1041_ = lean_array_uget_borrowed(v_buckets_1024_, v___x_1040_);
v___x_1042_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1021_, v_bkt_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; lean_object* v_size_x27_1044_; lean_object* v___x_1045_; lean_object* v_buckets_x27_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1043_ = lean_unsigned_to_nat(1u);
v_size_x27_1044_ = lean_nat_add(v_size_1023_, v___x_1043_);
lean_dec(v_size_1023_);
lean_inc(v_bkt_1041_);
v___x_1045_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1045_, 0, v_a_1021_);
lean_ctor_set(v___x_1045_, 1, v_b_1022_);
lean_ctor_set(v___x_1045_, 2, v_bkt_1041_);
v_buckets_x27_1046_ = lean_array_uset(v_buckets_1024_, v___x_1040_, v___x_1045_);
v___x_1047_ = lean_unsigned_to_nat(4u);
v___x_1048_ = lean_nat_mul(v_size_x27_1044_, v___x_1047_);
v___x_1049_ = lean_unsigned_to_nat(3u);
v___x_1050_ = lean_nat_div(v___x_1048_, v___x_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_array_get_size(v_buckets_x27_1046_);
v___x_1052_ = lean_nat_dec_le(v___x_1050_, v___x_1051_);
lean_dec(v___x_1050_);
if (v___x_1052_ == 0)
{
lean_object* v_val_1053_; lean_object* v___x_1055_; 
v_val_1053_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1046_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v_val_1053_);
lean_ctor_set(v___x_1026_, 0, v_size_x27_1044_);
v___x_1055_ = v___x_1026_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_size_x27_1044_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_val_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v___x_1058_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v_buckets_x27_1046_);
lean_ctor_set(v___x_1026_, 0, v_size_x27_1044_);
v___x_1058_ = v___x_1026_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_size_x27_1044_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_buckets_x27_1046_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v___x_1060_; lean_object* v_buckets_x27_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_inc(v_bkt_1041_);
v___x_1060_ = lean_box(0);
v_buckets_x27_1061_ = lean_array_uset(v_buckets_1024_, v___x_1040_, v___x_1060_);
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1021_, v_b_1022_, v_bkt_1041_);
v___x_1063_ = lean_array_uset(v_buckets_x27_1061_, v___x_1040_, v___x_1062_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 1, v___x_1063_);
v___x_1065_ = v___x_1026_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_size_1023_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1076_, size_t v_sz_1077_, size_t v_i_1078_, lean_object* v_b_1079_){
_start:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_usize_dec_lt(v_i_1078_, v_sz_1077_);
if (v___x_1080_ == 0)
{
return v_b_1079_;
}
else
{
lean_object* v_fst_1081_; lean_object* v_snd_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1132_; 
v_fst_1081_ = lean_ctor_get(v_b_1079_, 0);
v_snd_1082_ = lean_ctor_get(v_b_1079_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_b_1079_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1084_ = v_b_1079_;
v_isShared_1085_ = v_isSharedCheck_1132_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_snd_1082_);
lean_inc(v_fst_1081_);
lean_dec(v_b_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1132_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v_order_1089_; lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v_a_1105_; lean_object* v_filePath_1106_; lean_object* v___f_1107_; lean_object* v___x_1108_; 
v_a_1105_ = lean_array_uget_borrowed(v_as_1076_, v_i_1078_);
v_filePath_1106_ = lean_ctor_get(v_a_1105_, 0);
lean_inc_ref_n(v_filePath_1106_, 2);
v___f_1107_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1107_, 0, v_filePath_1106_);
v___x_1108_ = l_System_FilePath_extension(v_filePath_1106_);
if (lean_obj_tag(v___x_1108_) == 1)
{
lean_object* v_val_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_val_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_val_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___x_1110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1111_ = lean_string_dec_eq(v_val_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1112_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1113_ = lean_string_dec_eq(v_val_1109_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1115_ = lean_string_dec_eq(v_val_1109_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1117_ = lean_string_dec_eq(v_val_1109_, v___x_1116_);
lean_dec(v_val_1109_);
if (v___x_1117_ == 0)
{
lean_inc_ref(v_filePath_1106_);
v_fst_1101_ = v_filePath_1106_;
v_snd_1102_ = v___f_1107_;
goto v___jp_1100_;
}
else
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec_ref(v___f_1107_);
lean_inc_ref_n(v_filePath_1106_, 2);
v___f_1118_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1118_, 0, v_filePath_1106_);
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1120_ = l_System_FilePath_withExtension(v_filePath_1106_, v___x_1119_);
v___x_1121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1122_ = l_System_FilePath_withExtension(v___x_1120_, v___x_1121_);
v_fst_1101_ = v___x_1122_;
v_snd_1102_ = v___f_1118_;
goto v___jp_1100_;
}
}
else
{
lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
lean_dec(v_val_1109_);
lean_dec_ref(v___f_1107_);
lean_inc_ref_n(v_filePath_1106_, 2);
v___f_1123_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1123_, 0, v_filePath_1106_);
v___x_1124_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1125_ = l_System_FilePath_withExtension(v_filePath_1106_, v___x_1124_);
v_fst_1101_ = v___x_1125_;
v_snd_1102_ = v___f_1123_;
goto v___jp_1100_;
}
}
else
{
lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_dec(v_val_1109_);
lean_dec_ref(v___f_1107_);
lean_inc_ref_n(v_filePath_1106_, 2);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1126_, 0, v_filePath_1106_);
v___x_1127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1128_ = l_System_FilePath_withExtension(v_filePath_1106_, v___x_1127_);
v_fst_1101_ = v___x_1128_;
v_snd_1102_ = v___f_1126_;
goto v___jp_1100_;
}
}
else
{
lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec(v_val_1109_);
lean_dec_ref(v___f_1107_);
lean_inc_ref_n(v_filePath_1106_, 2);
v___f_1129_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1129_, 0, v_filePath_1106_);
v___x_1130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1131_ = l_System_FilePath_withExtension(v_filePath_1106_, v___x_1130_);
v_fst_1101_ = v___x_1131_;
v_snd_1102_ = v___f_1129_;
goto v___jp_1100_;
}
}
else
{
lean_dec(v___x_1108_);
lean_inc_ref(v_filePath_1106_);
v_fst_1101_ = v_filePath_1106_;
v_snd_1102_ = v___f_1107_;
goto v___jp_1100_;
}
v___jp_1086_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1091_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1082_, v___y_1087_, v___x_1090_);
v___x_1092_ = lean_apply_1(v___y_1088_, v___x_1091_);
v___x_1093_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1082_, v___y_1087_, v___x_1092_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1093_);
lean_ctor_set(v___x_1084_, 0, v_order_1089_);
v___x_1095_ = v___x_1084_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_order_1089_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
size_t v___x_1096_; size_t v___x_1097_; 
v___x_1096_ = ((size_t)1ULL);
v___x_1097_ = lean_usize_add(v_i_1078_, v___x_1096_);
v_i_1078_ = v___x_1097_;
v_b_1079_ = v___x_1095_;
goto _start;
}
}
v___jp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1082_, v_fst_1101_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
lean_inc_ref(v_fst_1101_);
v___x_1104_ = lean_array_push(v_fst_1081_, v_fst_1101_);
v___y_1087_ = v_fst_1101_;
v___y_1088_ = v_snd_1102_;
v_order_1089_ = v___x_1104_;
goto v___jp_1086_;
}
else
{
v___y_1087_ = v_fst_1101_;
v___y_1088_ = v_snd_1102_;
v_order_1089_ = v_fst_1081_;
goto v___jp_1086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1133_, lean_object* v_sz_1134_, lean_object* v_i_1135_, lean_object* v_b_1136_){
_start:
{
size_t v_sz_boxed_1137_; size_t v_i_boxed_1138_; lean_object* v_res_1139_; 
v_sz_boxed_1137_ = lean_unbox_usize(v_sz_1134_);
lean_dec(v_sz_1134_);
v_i_boxed_1138_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1133_, v_sz_boxed_1137_, v_i_boxed_1138_, v_b_1136_);
lean_dec_ref(v_as_1133_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1140_){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1142_ = lean_panic_fn_borrowed(v___x_1141_, v_msg_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1146_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1147_ = lean_unsigned_to_nat(11u);
v___x_1148_ = lean_unsigned_to_nat(163u);
v___x_1149_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1150_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1151_ = l_mkPanicMessageWithDecl(v___x_1150_, v___x_1149_, v___x_1148_, v___x_1147_, v___x_1146_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1152_, lean_object* v_x_1153_){
_start:
{
if (lean_obj_tag(v_x_1153_) == 0)
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1155_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1154_);
return v___x_1155_;
}
else
{
lean_object* v_key_1156_; lean_object* v_value_1157_; lean_object* v_tail_1158_; uint8_t v___x_1159_; 
v_key_1156_ = lean_ctor_get(v_x_1153_, 0);
v_value_1157_ = lean_ctor_get(v_x_1153_, 1);
v_tail_1158_ = lean_ctor_get(v_x_1153_, 2);
v___x_1159_ = lean_string_dec_eq(v_key_1156_, v_a_1152_);
if (v___x_1159_ == 0)
{
v_x_1153_ = v_tail_1158_;
goto _start;
}
else
{
lean_inc(v_value_1157_);
return v_value_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1161_, v_x_1162_);
lean_dec(v_x_1162_);
lean_dec_ref(v_a_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_buckets_1166_; lean_object* v___x_1167_; uint64_t v___x_1168_; uint64_t v___x_1169_; uint64_t v___x_1170_; uint64_t v_fold_1171_; uint64_t v___x_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; size_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_buckets_1166_ = lean_ctor_get(v_m_1164_, 1);
v___x_1167_ = lean_array_get_size(v_buckets_1166_);
v___x_1168_ = lean_string_hash(v_a_1165_);
v___x_1169_ = 32ULL;
v___x_1170_ = lean_uint64_shift_right(v___x_1168_, v___x_1169_);
v_fold_1171_ = lean_uint64_xor(v___x_1168_, v___x_1170_);
v___x_1172_ = 16ULL;
v___x_1173_ = lean_uint64_shift_right(v_fold_1171_, v___x_1172_);
v___x_1174_ = lean_uint64_xor(v_fold_1171_, v___x_1173_);
v___x_1175_ = lean_uint64_to_usize(v___x_1174_);
v___x_1176_ = lean_usize_of_nat(v___x_1167_);
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_sub(v___x_1176_, v___x_1177_);
v___x_1179_ = lean_usize_land(v___x_1175_, v___x_1178_);
v___x_1180_ = lean_array_uget_borrowed(v_buckets_1166_, v___x_1179_);
v___x_1181_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1165_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1182_, v_a_1183_);
lean_dec_ref(v_a_1183_);
lean_dec_ref(v_m_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1185_, size_t v_sz_1186_, size_t v_i_1187_, lean_object* v_bs_1188_){
_start:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_usize_dec_lt(v_i_1187_, v_sz_1186_);
if (v___x_1189_ == 0)
{
return v_bs_1188_;
}
else
{
lean_object* v_v_1190_; lean_object* v___x_1191_; lean_object* v_bs_x27_1192_; lean_object* v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; lean_object* v___x_1196_; 
v_v_1190_ = lean_array_uget(v_bs_1188_, v_i_1187_);
v___x_1191_ = lean_unsigned_to_nat(0u);
v_bs_x27_1192_ = lean_array_uset(v_bs_1188_, v_i_1187_, v___x_1191_);
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1185_, v_v_1190_);
lean_dec(v_v_1190_);
v___x_1194_ = ((size_t)1ULL);
v___x_1195_ = lean_usize_add(v_i_1187_, v___x_1194_);
v___x_1196_ = lean_array_uset(v_bs_x27_1192_, v_i_1187_, v___x_1193_);
v_i_1187_ = v___x_1195_;
v_bs_1188_ = v___x_1196_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1198_, lean_object* v_sz_1199_, lean_object* v_i_1200_, lean_object* v_bs_1201_){
_start:
{
size_t v_sz_boxed_1202_; size_t v_i_boxed_1203_; lean_object* v_res_1204_; 
v_sz_boxed_1202_ = lean_unbox_usize(v_sz_1199_);
lean_dec(v_sz_1199_);
v_i_boxed_1203_ = lean_unbox_usize(v_i_1200_);
lean_dec(v_i_1200_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1198_, v_sz_boxed_1202_, v_i_boxed_1203_, v_bs_1201_);
lean_dec_ref(v___x_1198_);
return v_res_1204_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_unsigned_to_nat(16u);
v___x_1209_ = lean_mk_array(v___x_1208_, v___x_1207_);
return v___x_1209_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_byBase_1212_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1211_ = lean_unsigned_to_nat(0u);
v_byBase_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1212_, 0, v___x_1211_);
lean_ctor_set(v_byBase_1212_, 1, v___x_1210_);
return v_byBase_1212_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1213_; lean_object* v_order_1214_; lean_object* v___x_1215_; 
v_byBase_1213_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1214_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_order_1214_);
lean_ctor_set(v___x_1215_, 1, v_byBase_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1216_){
_start:
{
lean_object* v___x_1217_; size_t v_sz_1218_; size_t v___x_1219_; lean_object* v___x_1220_; lean_object* v_fst_1221_; lean_object* v_snd_1222_; size_t v_sz_1223_; lean_object* v___x_1224_; 
v___x_1217_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1218_ = lean_array_size(v_regions_1216_);
v___x_1219_ = ((size_t)0ULL);
v___x_1220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1216_, v_sz_1218_, v___x_1219_, v___x_1217_);
v_fst_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_fst_1221_);
v_snd_1222_ = lean_ctor_get(v___x_1220_, 1);
lean_inc(v_snd_1222_);
lean_dec_ref(v___x_1220_);
v_sz_1223_ = lean_array_size(v_fst_1221_);
v___x_1224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1222_, v_sz_1223_, v___x_1219_, v_fst_1221_);
lean_dec(v_snd_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1225_);
lean_dec_ref(v_regions_1225_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1227_, lean_object* v_m_1228_, lean_object* v_a_1229_, lean_object* v_fallback_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1228_, v_a_1229_, v_fallback_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1232_, lean_object* v_m_1233_, lean_object* v_a_1234_, lean_object* v_fallback_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1232_, v_m_1233_, v_a_1234_, v_fallback_1235_);
lean_dec(v_fallback_1235_);
lean_dec_ref(v_a_1234_);
lean_dec_ref(v_m_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1237_, lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1238_, v_a_1239_, v_b_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1242_, lean_object* v_m_1243_, lean_object* v_a_1244_){
_start:
{
uint8_t v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1243_, v_a_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_m_1247_, lean_object* v_a_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1246_, v_m_1247_, v_a_1248_);
lean_dec_ref(v_a_1248_);
lean_dec_ref(v_m_1247_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1251_, lean_object* v_a_1252_, lean_object* v_fallback_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1252_, v_fallback_1253_, v_x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1256_, lean_object* v_a_1257_, lean_object* v_fallback_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1256_, v_a_1257_, v_fallback_1258_, v_x_1259_);
lean_dec(v_x_1259_);
lean_dec(v_fallback_1258_);
lean_dec_ref(v_a_1257_);
return v_res_1260_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1261_, lean_object* v_a_1262_, lean_object* v_x_1263_){
_start:
{
uint8_t v___x_1264_; 
v___x_1264_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1265_, lean_object* v_a_1266_, lean_object* v_x_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1265_, v_a_1266_, v_x_1267_);
lean_dec(v_x_1267_);
lean_dec_ref(v_a_1266_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1270_, lean_object* v_data_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1273_, lean_object* v_a_1274_, lean_object* v_b_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1274_, v_b_1275_, v_x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1278_, lean_object* v_i_1279_, lean_object* v_source_1280_, lean_object* v_target_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1279_, v_source_1280_, v_target_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1284_, v_x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1287_, size_t v_sz_1288_, size_t v_i_1289_, lean_object* v_b_1290_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_lt(v_i_1289_, v_sz_1288_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_b_1290_);
return v___x_1293_;
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1295_; 
v_a_1294_ = lean_array_uget_borrowed(v_as_1287_, v_i_1289_);
v___x_1295_ = lean_compacted_region_read(v_a_1294_, v_b_1290_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v_snd_1297_; lean_object* v___x_1298_; size_t v___x_1299_; size_t v___x_1300_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v_snd_1297_ = lean_ctor_get(v_a_1296_, 1);
lean_inc(v_snd_1297_);
lean_dec(v_a_1296_);
v___x_1298_ = lean_array_push(v_b_1290_, v_snd_1297_);
v___x_1299_ = ((size_t)1ULL);
v___x_1300_ = lean_usize_add(v_i_1289_, v___x_1299_);
v_i_1289_ = v___x_1300_;
v_b_1290_ = v___x_1298_;
goto _start;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec_ref(v_b_1290_);
v_a_1302_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1295_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1295_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1310_, lean_object* v_sz_1311_, lean_object* v_i_1312_, lean_object* v_b_1313_, lean_object* v___y_1314_){
_start:
{
size_t v_sz_boxed_1315_; size_t v_i_boxed_1316_; lean_object* v_res_1317_; 
v_sz_boxed_1315_ = lean_unbox_usize(v_sz_1311_);
lean_dec(v_sz_1311_);
v_i_boxed_1316_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1310_, v_sz_boxed_1315_, v_i_boxed_1316_, v_b_1313_);
lean_dec_ref(v_as_1310_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1320_){
_start:
{
lean_object* v_oleanRegions_1322_; lean_object* v___x_1323_; size_t v_sz_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v_oleanRegions_1322_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1320_);
v___x_1323_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1320_);
v_sz_1324_ = lean_array_size(v___x_1323_);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1323_, v_sz_1324_, v___x_1325_, v_oleanRegions_1322_);
lean_dec_ref(v___x_1323_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1328_; size_t v_sz_1329_; lean_object* v___x_1330_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = l_Lean_ModuleArtifacts_irParts(v_arts_1320_);
v_sz_1329_ = lean_array_size(v___x_1328_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1328_, v_sz_1329_, v___x_1325_, v_oleanRegions_1322_);
lean_dec_ref(v___x_1328_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = l_Array_append___redArg(v_a_1327_, v_a_1331_);
lean_dec(v_a_1331_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_dec(v_a_1327_);
return v___x_1330_;
}
}
else
{
lean_dec_ref(v_arts_1320_);
return v___x_1326_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1340_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1343_){
_start:
{
if (lean_obj_tag(v_e_1343_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1354_; 
v_a_1345_ = lean_ctor_get(v_e_1343_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_e_1343_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1347_ = v_e_1343_;
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v_e_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1354_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = lean_io_error_to_string(v_a_1345_);
v___x_1350_ = lean_mk_io_user_error(v___x_1349_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1350_);
v___x_1352_ = v___x_1347_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v_e_1343_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v_e_1343_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v_e_1343_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v_e_1343_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set_tag(v___x_1357_, 0);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1363_, lean_object* v_a_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1366_, lean_object* v_e_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_e_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1370_, v_e_1371_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1374_, lean_object* v___y_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1407_; 
v_fst_1378_ = lean_ctor_get(v_a_1376_, 0);
v_snd_1379_ = lean_ctor_get(v_a_1376_, 1);
v_isSharedCheck_1407_ = !lean_is_exclusive(v_a_1376_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1381_ = v_a_1376_;
v_isShared_1382_ = v_isSharedCheck_1407_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_snd_1379_);
lean_inc(v_fst_1378_);
lean_dec(v_a_1376_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1407_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = lean_array_get_size(v_a_1374_);
v___x_1384_ = lean_nat_dec_lt(v_snd_1379_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1386_; 
if (v_isShared_1382_ == 0)
{
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_fst_1378_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_snd_1379_);
v___x_1386_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1390_ = lean_array_get_borrowed(v___x_1389_, v_a_1374_, v_snd_1379_);
lean_inc(v___x_1390_);
v___x_1391_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = l_Array_append___redArg(v_fst_1378_, v_a_1392_);
lean_dec(v_a_1392_);
v___x_1394_ = lean_nat_add(v_snd_1379_, v___y_1375_);
lean_dec(v_snd_1379_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1394_);
lean_ctor_set(v___x_1381_, 0, v___x_1393_);
v___x_1396_ = v___x_1381_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
v_a_1376_ = v___x_1396_;
goto _start;
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_del_object(v___x_1381_);
lean_dec(v_snd_1379_);
lean_dec(v_fst_1378_);
v_a_1399_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1391_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1391_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1408_, lean_object* v___y_1409_, lean_object* v_a_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1408_, v___y_1409_, v_a_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v_a_1408_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1413_, lean_object* v___y_1414_, lean_object* v___x_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1413_, v___y_1414_, v___x_1415_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1426_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1426_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_fst_1422_; lean_object* v___x_1424_; 
v_fst_1422_ = lean_ctor_get(v_a_1418_, 0);
lean_inc(v_fst_1422_);
lean_dec(v_a_1418_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 1);
lean_ctor_set(v___x_1420_, 0, v_fst_1422_);
v___x_1424_ = v___x_1420_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_fst_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1417_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1417_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 0);
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1435_, lean_object* v___y_1436_, lean_object* v___x_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1435_, v___y_1436_, v___x_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v_a_1435_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1440_, lean_object* v_a_1441_, lean_object* v___y_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_){
_start:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_nat_dec_lt(v_a_1443_, v_upperBound_1440_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; 
lean_dec(v_a_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v_a_1441_);
v___x_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1444_);
return v___x_1447_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1448_ = lean_unsigned_to_nat(0u);
v___x_1449_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1443_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_a_1443_);
lean_inc(v___y_1442_);
lean_inc_ref(v_a_1441_);
v___f_1451_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1451_, 0, v_a_1441_);
lean_closure_set(v___f_1451_, 1, v___y_1442_);
lean_closure_set(v___f_1451_, 2, v___x_1450_);
v___x_1452_ = lean_io_as_task(v___f_1451_, v___x_1448_);
v___x_1453_ = lean_array_push(v_b_1444_, v___x_1452_);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_a_1443_, v___x_1454_);
lean_dec(v_a_1443_);
v_a_1443_ = v___x_1455_;
v_b_1444_ = v___x_1453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1457_, lean_object* v_a_1458_, lean_object* v___y_1459_, lean_object* v_a_1460_, lean_object* v_b_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1457_, v_a_1458_, v___y_1459_, v_a_1460_, v_b_1461_);
lean_dec(v_upperBound_1457_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1464_, size_t v_sz_1465_, size_t v_i_1466_, lean_object* v_b_1467_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = lean_usize_dec_lt(v_i_1466_, v_sz_1465_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1470_, 0, v_b_1467_);
return v___x_1470_;
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v_a_1471_ = lean_array_uget_borrowed(v_as_1464_, v_i_1466_);
lean_inc(v_a_1471_);
v___x_1472_ = lean_task_get_own(v_a_1471_);
v___x_1473_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; size_t v___x_1476_; size_t v___x_1477_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = l_Array_append___redArg(v_b_1467_, v_a_1474_);
lean_dec(v_a_1474_);
v___x_1476_ = ((size_t)1ULL);
v___x_1477_ = lean_usize_add(v_i_1466_, v___x_1476_);
v_i_1466_ = v___x_1477_;
v_b_1467_ = v___x_1475_;
goto _start;
}
else
{
lean_dec_ref(v_b_1467_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1479_, lean_object* v_sz_1480_, lean_object* v_i_1481_, lean_object* v_b_1482_, lean_object* v___y_1483_){
_start:
{
size_t v_sz_boxed_1484_; size_t v_i_boxed_1485_; lean_object* v_res_1486_; 
v_sz_boxed_1484_ = lean_unbox_usize(v_sz_1480_);
lean_dec(v_sz_1480_);
v_i_boxed_1485_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1479_, v_sz_boxed_1484_, v_i_boxed_1485_, v_b_1482_);
lean_dec_ref(v_as_1479_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1487_, size_t v_i_1488_, lean_object* v_bs_1489_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1488_, v_sz_1487_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_bs_1489_);
return v___x_1491_;
}
else
{
lean_object* v_v_1492_; lean_object* v___x_1493_; 
v_v_1492_ = lean_array_uget_borrowed(v_bs_1489_, v_i_1488_);
lean_inc(v_v_1492_);
v___x_1493_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1492_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec_ref(v_bs_1489_);
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v_bs_x27_1504_; size_t v___x_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v_a_1502_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1503_ = lean_unsigned_to_nat(0u);
v_bs_x27_1504_ = lean_array_uset(v_bs_1489_, v_i_1488_, v___x_1503_);
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1488_, v___x_1505_);
v___x_1507_ = lean_array_uset(v_bs_x27_1504_, v_i_1488_, v_a_1502_);
v_i_1488_ = v___x_1506_;
v_bs_1489_ = v___x_1507_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1509_, lean_object* v_i_1510_, lean_object* v_bs_1511_){
_start:
{
size_t v_sz_boxed_1512_; size_t v_i_boxed_1513_; lean_object* v_res_1514_; 
v_sz_boxed_1512_ = lean_unbox_usize(v_sz_1509_);
lean_dec(v_sz_1509_);
v_i_boxed_1513_ = lean_unbox_usize(v_i_1510_);
lean_dec(v_i_1510_);
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1512_, v_i_boxed_1513_, v_bs_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1517_){
_start:
{
if (lean_obj_tag(v_x_1517_) == 4)
{
lean_object* v_elems_1518_; size_t v_sz_1519_; size_t v___x_1520_; lean_object* v___x_1521_; 
v_elems_1518_ = lean_ctor_get(v_x_1517_, 0);
lean_inc_ref(v_elems_1518_);
lean_dec_ref_known(v_x_1517_, 1);
v_sz_1519_ = lean_array_size(v_elems_1518_);
v___x_1520_ = ((size_t)0ULL);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1519_, v___x_1520_, v_elems_1518_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1522_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1523_ = lean_unsigned_to_nat(80u);
v___x_1524_ = l_Lean_Json_pretty(v_x_1517_, v___x_1523_);
v___x_1525_ = lean_string_append(v___x_1522_, v___x_1524_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1527_ = lean_string_append(v___x_1525_, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1532_; uint32_t v___x_1533_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_internal_get_hardware_concurrency(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1535_ = lean_uint32_to_nat(v___x_1534_);
return v___x_1535_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1537_ = lean_unsigned_to_nat(4u);
v___x_1538_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1539_ = lean_nat_dec_le(v___x_1538_, v___x_1537_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v_depsFile_1543_; lean_object* v___x_1544_; 
v___x_1542_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1540_);
v_depsFile_1543_ = l_System_FilePath_addExtension(v_fname_1540_, v___x_1542_);
v___x_1544_ = l_IO_FS_readFile(v_depsFile_1543_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1631_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1631_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1631_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_a_1550_; lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Json_parse(v_a_1545_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; 
lean_dec_ref(v_fname_1540_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v_a_1550_ = v_a_1561_;
goto v___jp_1549_;
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1562_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1563_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1562_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; 
lean_dec_ref(v_fname_1540_);
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1563_, 1);
v_a_1550_ = v_a_1564_;
goto v___jp_1549_;
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1569_; lean_object* v___y_1616_; lean_object* v___y_1617_; lean_object* v___y_1620_; uint8_t v___x_1630_; 
lean_del_object(v___x_1547_);
lean_dec_ref(v_depsFile_1543_);
v_a_1565_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1563_, 1);
v___x_1566_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1567_ = lean_unsigned_to_nat(4u);
v___x_1630_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1630_ == 0)
{
v___y_1620_ = v___x_1567_;
goto v___jp_1619_;
}
else
{
v___y_1620_ = v___x_1566_;
goto v___jp_1619_;
}
v___jp_1568_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_mk_empty_array_with_capacity(v___y_1569_);
v___x_1571_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1565_);
lean_inc(v___y_1569_);
v___x_1572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1569_, v_a_1565_, v___y_1569_, v___x_1571_, v___x_1570_);
lean_dec(v___y_1569_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; size_t v_sz_1577_; size_t v___x_1578_; lean_object* v___x_1579_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = lean_array_get_size(v_a_1565_);
lean_dec(v_a_1565_);
v___x_1575_ = lean_nat_mul(v___x_1574_, v___x_1567_);
v___x_1576_ = lean_mk_empty_array_with_capacity(v___x_1575_);
lean_dec(v___x_1575_);
v_sz_1577_ = lean_array_size(v_a_1573_);
v___x_1578_ = ((size_t)0ULL);
v___x_1579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1573_, v_sz_1577_, v___x_1578_, v___x_1576_);
lean_dec(v_a_1573_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = lean_compacted_region_read(v_fname_1540_, v_a_1580_);
lean_dec(v_a_1580_);
lean_dec_ref(v_fname_1540_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_fst_1586_; lean_object* v___x_1588_; 
v_fst_1586_ = lean_ctor_get(v_a_1582_, 0);
lean_inc(v_fst_1586_);
lean_dec(v_a_1582_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v_fst_1586_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_fst_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
else
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_a_1591_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1593_ = v___x_1581_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1581_);
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
lean_dec_ref(v_fname_1540_);
v_a_1599_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1579_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1579_);
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
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_a_1565_);
lean_dec_ref(v_fname_1540_);
v_a_1607_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1572_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1572_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
v___jp_1615_:
{
uint8_t v___x_1618_; 
v___x_1618_ = lean_nat_dec_le(v___y_1616_, v___y_1617_);
if (v___x_1618_ == 0)
{
lean_dec(v___y_1617_);
v___y_1569_ = v___y_1616_;
goto v___jp_1568_;
}
else
{
lean_dec(v___y_1616_);
v___y_1569_ = v___y_1617_;
goto v___jp_1568_;
}
}
v___jp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1622_ = lean_io_getenv(v___x_1621_);
v___x_1623_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1622_) == 0)
{
v___y_1616_ = v___x_1623_;
v___y_1617_ = v___y_1620_;
goto v___jp_1615_;
}
else
{
lean_object* v_val_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_val_1624_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1622_, 1);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = lean_string_utf8_byte_size(v_val_1624_);
v___x_1627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1627_, 0, v_val_1624_);
lean_ctor_set(v___x_1627_, 1, v___x_1625_);
lean_ctor_set(v___x_1627_, 2, v___x_1626_);
v___x_1628_ = l_String_Slice_toNat_x3f(v___x_1627_);
lean_dec_ref_known(v___x_1627_, 3);
if (lean_obj_tag(v___x_1628_) == 0)
{
v___y_1616_ = v___x_1623_;
v___y_1617_ = v___y_1620_;
goto v___jp_1615_;
}
else
{
lean_object* v_val_1629_; 
lean_dec(v___y_1620_);
v_val_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_val_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v___y_1616_ = v___x_1623_;
v___y_1617_ = v_val_1629_;
goto v___jp_1615_;
}
}
}
}
}
v___jp_1549_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1552_ = lean_string_append(v___x_1551_, v_depsFile_1543_);
lean_dec_ref(v_depsFile_1543_);
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1554_ = lean_string_append(v___x_1552_, v___x_1553_);
v___x_1555_ = lean_string_append(v___x_1554_, v_a_1550_);
lean_dec_ref(v_a_1550_);
v___x_1556_ = lean_mk_io_user_error(v___x_1555_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 1);
lean_ctor_set(v___x_1547_, 0, v___x_1556_);
v___x_1558_ = v___x_1547_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_depsFile_1543_);
lean_dec_ref(v_fname_1540_);
v_a_1632_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1544_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1544_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1643_, lean_object* v___y_1644_, lean_object* v_inst_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1643_, v___y_1644_, v_a_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1649_, lean_object* v___y_1650_, lean_object* v_inst_1651_, lean_object* v_a_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1649_, v___y_1650_, v_inst_1651_, v_a_1652_);
lean_dec(v___y_1650_);
lean_dec_ref(v_a_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1655_, lean_object* v_a_1656_, lean_object* v___y_1657_, lean_object* v_inst_1658_, lean_object* v_R_1659_, lean_object* v_a_1660_, lean_object* v_b_1661_, lean_object* v_c_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1655_, v_a_1656_, v___y_1657_, v_a_1660_, v_b_1661_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1665_, lean_object* v_a_1666_, lean_object* v___y_1667_, lean_object* v_inst_1668_, lean_object* v_R_1669_, lean_object* v_a_1670_, lean_object* v_b_1671_, lean_object* v_c_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1665_, v_a_1666_, v___y_1667_, v_inst_1668_, v_R_1669_, v_a_1670_, v_b_1671_, v_c_1672_);
lean_dec(v_upperBound_1665_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1675_, size_t v_sz_1676_, size_t v_i_1677_, lean_object* v_b_1678_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_lt(v_i_1677_, v_sz_1676_);
if (v___x_1680_ == 0)
{
return v_b_1678_;
}
else
{
lean_object* v_a_1681_; lean_object* v_cancelTk_x3f_1682_; lean_object* v___x_1683_; 
v_a_1681_ = lean_array_uget_borrowed(v_as_1675_, v_i_1677_);
v_cancelTk_x3f_1682_ = lean_ctor_get(v_a_1681_, 2);
v___x_1683_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1682_) == 1)
{
lean_object* v_val_1690_; lean_object* v___x_1691_; 
v_val_1690_ = lean_ctor_get(v_cancelTk_x3f_1682_, 0);
v___x_1691_ = l_IO_CancelToken_set(v_val_1690_);
goto v___jp_1684_;
}
else
{
goto v___jp_1684_;
}
v___jp_1684_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; 
lean_inc(v_a_1681_);
v___x_1685_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1681_);
v___x_1686_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1685_);
lean_dec(v___x_1685_);
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_add(v_i_1677_, v___x_1687_);
v_i_1677_ = v___x_1688_;
v_b_1678_ = v___x_1683_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1692_){
_start:
{
lean_object* v_children_1694_; lean_object* v___x_1695_; size_t v_sz_1696_; size_t v___x_1697_; lean_object* v___x_1698_; 
v_children_1694_ = lean_ctor_get(v_s_1692_, 1);
v___x_1695_ = lean_box(0);
v_sz_1696_ = lean_array_size(v_children_1694_);
v___x_1697_ = ((size_t)0ULL);
v___x_1698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1694_, v_sz_1696_, v___x_1697_, v___x_1695_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1699_);
lean_dec_ref(v_s_1699_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1702_, lean_object* v_sz_1703_, lean_object* v_i_1704_, lean_object* v_b_1705_, lean_object* v___y_1706_){
_start:
{
size_t v_sz_boxed_1707_; size_t v_i_boxed_1708_; lean_object* v_res_1709_; 
v_sz_boxed_1707_ = lean_unbox_usize(v_sz_1703_);
lean_dec(v_sz_1703_);
v_i_boxed_1708_ = lean_unbox_usize(v_i_1704_);
lean_dec(v_i_1704_);
v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1702_, v_sz_boxed_1707_, v_i_boxed_1708_, v_b_1705_);
lean_dec_ref(v_as_1702_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1710_, lean_object* v_m_1711_){
_start:
{
lean_object* v_result_x3f_1712_; 
v_result_x3f_1712_ = lean_ctor_get(v_snap_1710_, 4);
lean_inc(v_result_x3f_1712_);
if (lean_obj_tag(v_result_x3f_1712_) == 1)
{
lean_object* v_val_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1813_; 
v_val_1713_ = lean_ctor_get(v_result_x3f_1712_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_result_x3f_1712_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1715_ = v_result_x3f_1712_;
v_isShared_1716_ = v_isSharedCheck_1813_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_val_1713_);
lean_dec(v_result_x3f_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1813_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_toSnapshot_1717_; lean_object* v_metaSnap_1718_; lean_object* v_ictx_1719_; lean_object* v_stx_1720_; lean_object* v_parserState_1721_; lean_object* v_processedSnap_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1812_; 
v_toSnapshot_1717_ = lean_ctor_get(v_snap_1710_, 0);
v_metaSnap_1718_ = lean_ctor_get(v_snap_1710_, 1);
v_ictx_1719_ = lean_ctor_get(v_snap_1710_, 2);
v_stx_1720_ = lean_ctor_get(v_snap_1710_, 3);
v_parserState_1721_ = lean_ctor_get(v_val_1713_, 0);
v_processedSnap_1722_ = lean_ctor_get(v_val_1713_, 1);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_val_1713_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1724_ = v_val_1713_;
v_isShared_1725_ = v_isSharedCheck_1812_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_processedSnap_1722_);
lean_inc(v_parserState_1721_);
lean_dec(v_val_1713_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1812_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_processed_1726_; lean_object* v_result_x3f_1727_; 
v_processed_1726_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1722_);
v_result_x3f_1727_ = lean_ctor_get(v_processed_1726_, 2);
lean_inc(v_result_x3f_1727_);
if (lean_obj_tag(v_result_x3f_1727_) == 1)
{
lean_object* v_val_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1811_; 
v_val_1728_ = lean_ctor_get(v_result_x3f_1727_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_result_x3f_1727_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1730_ = v_result_x3f_1727_;
v_isShared_1731_ = v_isSharedCheck_1811_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_val_1728_);
lean_dec(v_result_x3f_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1811_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_cmdState_1732_; lean_object* v_toSnapshot_1733_; lean_object* v_metaSnap_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1809_; 
v_cmdState_1732_ = lean_ctor_get(v_val_1728_, 0);
lean_inc_ref(v_cmdState_1732_);
v_toSnapshot_1733_ = lean_ctor_get(v_processed_1726_, 0);
v_metaSnap_1734_ = lean_ctor_get(v_processed_1726_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_processed_1726_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_processed_1726_, 2);
lean_dec(v_unused_1810_);
v___x_1736_ = v_processed_1726_;
v_isShared_1737_ = v_isSharedCheck_1809_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_metaSnap_1734_);
lean_inc(v_toSnapshot_1733_);
lean_dec(v_processed_1726_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1809_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_firstCmdSnap_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1807_; 
v_firstCmdSnap_1738_ = lean_ctor_get(v_val_1728_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_val_1728_);
if (v_isSharedCheck_1807_ == 0)
{
lean_object* v_unused_1808_; 
v_unused_1808_ = lean_ctor_get(v_val_1728_, 0);
lean_dec(v_unused_1808_);
v___x_1740_ = v_val_1728_;
v_isShared_1741_ = v_isSharedCheck_1807_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_firstCmdSnap_1738_);
lean_dec(v_val_1728_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1807_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_env_1742_; lean_object* v_messages_1743_; lean_object* v_scopes_1744_; lean_object* v_usedQuotCtxts_1745_; lean_object* v_nextMacroScope_1746_; lean_object* v_maxRecDepth_1747_; lean_object* v_ngen_1748_; lean_object* v_auxDeclNGen_1749_; lean_object* v_infoState_1750_; lean_object* v_traceState_1751_; lean_object* v_snapshotTasks_1752_; lean_object* v_prevLinterStates_1753_; lean_object* v_codeQualityEntryTasks_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1806_; 
v_env_1742_ = lean_ctor_get(v_cmdState_1732_, 0);
v_messages_1743_ = lean_ctor_get(v_cmdState_1732_, 1);
v_scopes_1744_ = lean_ctor_get(v_cmdState_1732_, 2);
v_usedQuotCtxts_1745_ = lean_ctor_get(v_cmdState_1732_, 3);
v_nextMacroScope_1746_ = lean_ctor_get(v_cmdState_1732_, 4);
v_maxRecDepth_1747_ = lean_ctor_get(v_cmdState_1732_, 5);
v_ngen_1748_ = lean_ctor_get(v_cmdState_1732_, 6);
v_auxDeclNGen_1749_ = lean_ctor_get(v_cmdState_1732_, 7);
v_infoState_1750_ = lean_ctor_get(v_cmdState_1732_, 8);
v_traceState_1751_ = lean_ctor_get(v_cmdState_1732_, 9);
v_snapshotTasks_1752_ = lean_ctor_get(v_cmdState_1732_, 10);
v_prevLinterStates_1753_ = lean_ctor_get(v_cmdState_1732_, 11);
v_codeQualityEntryTasks_1754_ = lean_ctor_get(v_cmdState_1732_, 12);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_cmdState_1732_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1756_ = v_cmdState_1732_;
v_isShared_1757_ = v_isSharedCheck_1806_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1754_);
lean_inc(v_prevLinterStates_1753_);
lean_inc(v_snapshotTasks_1752_);
lean_inc(v_traceState_1751_);
lean_inc(v_infoState_1750_);
lean_inc(v_auxDeclNGen_1749_);
lean_inc(v_ngen_1748_);
lean_inc(v_maxRecDepth_1747_);
lean_inc(v_nextMacroScope_1746_);
lean_inc(v_usedQuotCtxts_1745_);
lean_inc(v_scopes_1744_);
lean_inc(v_messages_1743_);
lean_inc(v_env_1742_);
lean_dec(v_cmdState_1732_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1806_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1758_; lean_object* v_mainModule_1759_; uint8_t v___x_1760_; 
v___x_1758_ = l_Lean_Environment_header(v_env_1742_);
v_mainModule_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_mainModule_1759_);
lean_dec_ref(v___x_1758_);
v___x_1760_ = lean_name_eq(v_mainModule_1759_, v_m_1711_);
lean_dec(v_mainModule_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1800_; 
lean_inc(v_stx_1720_);
lean_inc_ref(v_ictx_1719_);
lean_inc_ref(v_metaSnap_1718_);
lean_inc_ref(v_toSnapshot_1717_);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_snap_1710_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; lean_object* v_unused_1802_; lean_object* v_unused_1803_; lean_object* v_unused_1804_; lean_object* v_unused_1805_; 
v_unused_1801_ = lean_ctor_get(v_snap_1710_, 4);
lean_dec(v_unused_1801_);
v_unused_1802_ = lean_ctor_get(v_snap_1710_, 3);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_snap_1710_, 2);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v_snap_1710_, 1);
lean_dec(v_unused_1804_);
v_unused_1805_ = lean_ctor_get(v_snap_1710_, 0);
lean_dec(v_unused_1805_);
v___x_1762_ = v_snap_1710_;
v_isShared_1763_ = v_isSharedCheck_1800_;
goto v_resetjp_1761_;
}
else
{
lean_dec(v_snap_1710_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1800_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_idx_1764_; lean_object* v_parentIdxs_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1798_; 
v_idx_1764_ = lean_ctor_get(v_auxDeclNGen_1749_, 1);
v_parentIdxs_1765_ = lean_ctor_get(v_auxDeclNGen_1749_, 2);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_auxDeclNGen_1749_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_auxDeclNGen_1749_, 0);
lean_dec(v_unused_1799_);
v___x_1767_ = v_auxDeclNGen_1749_;
v_isShared_1768_ = v_isSharedCheck_1798_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_parentIdxs_1765_);
lean_inc(v_idx_1764_);
lean_dec(v_auxDeclNGen_1749_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1798_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_newEnv_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
v_newEnv_1769_ = l_Lean_Environment_setMainModule(v_env_1742_, v_m_1711_);
v___x_1770_ = lean_box(0);
v___x_1771_ = l_Lean_mkPrivateName(v_newEnv_1769_, v___x_1770_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1771_);
v___x_1773_ = v___x_1767_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_idx_1764_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_parentIdxs_1765_);
v___x_1773_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v_newCmdState_1775_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 7, v___x_1773_);
lean_ctor_set(v___x_1756_, 0, v_newEnv_1769_);
v_newCmdState_1775_ = v___x_1756_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_newEnv_1769_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_messages_1743_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_scopes_1744_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_usedQuotCtxts_1745_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_nextMacroScope_1746_);
lean_ctor_set(v_reuseFailAlloc_1796_, 5, v_maxRecDepth_1747_);
lean_ctor_set(v_reuseFailAlloc_1796_, 6, v_ngen_1748_);
lean_ctor_set(v_reuseFailAlloc_1796_, 7, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1796_, 8, v_infoState_1750_);
lean_ctor_set(v_reuseFailAlloc_1796_, 9, v_traceState_1751_);
lean_ctor_set(v_reuseFailAlloc_1796_, 10, v_snapshotTasks_1752_);
lean_ctor_set(v_reuseFailAlloc_1796_, 11, v_prevLinterStates_1753_);
lean_ctor_set(v_reuseFailAlloc_1796_, 12, v_codeQualityEntryTasks_1754_);
v_newCmdState_1775_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v_newCmdState_1775_);
v___x_1777_ = v___x_1740_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_newCmdState_1775_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_firstCmdSnap_1738_);
v___x_1777_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1777_);
v___x_1779_ = v___x_1730_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v_newProcessed_1781_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 2, v___x_1779_);
v_newProcessed_1781_ = v___x_1736_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_toSnapshot_1733_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_metaSnap_1734_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v___x_1779_);
v_newProcessed_1781_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_box(0);
v___x_1783_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1782_, v_newProcessed_1781_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v___x_1783_);
v___x_1785_ = v___x_1724_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_parserState_1721_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1785_);
v___x_1787_ = v___x_1715_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1789_; 
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 4, v___x_1787_);
v___x_1789_ = v___x_1762_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_toSnapshot_1717_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_metaSnap_1718_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_ictx_1719_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_stx_1720_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
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
lean_del_object(v___x_1756_);
lean_dec_ref(v_codeQualityEntryTasks_1754_);
lean_dec(v_prevLinterStates_1753_);
lean_dec_ref(v_snapshotTasks_1752_);
lean_dec_ref(v_traceState_1751_);
lean_dec_ref(v_infoState_1750_);
lean_dec_ref(v_auxDeclNGen_1749_);
lean_dec_ref(v_ngen_1748_);
lean_dec(v_maxRecDepth_1747_);
lean_dec(v_nextMacroScope_1746_);
lean_dec(v_usedQuotCtxts_1745_);
lean_dec(v_scopes_1744_);
lean_dec_ref(v_messages_1743_);
lean_dec_ref(v_env_1742_);
lean_del_object(v___x_1740_);
lean_dec_ref(v_firstCmdSnap_1738_);
lean_del_object(v___x_1736_);
lean_dec_ref(v_metaSnap_1734_);
lean_dec_ref(v_toSnapshot_1733_);
lean_del_object(v___x_1730_);
lean_del_object(v___x_1724_);
lean_dec_ref(v_parserState_1721_);
lean_del_object(v___x_1715_);
lean_dec(v_m_1711_);
return v_snap_1710_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1727_);
lean_dec(v_processed_1726_);
lean_del_object(v___x_1724_);
lean_dec_ref(v_parserState_1721_);
lean_del_object(v___x_1715_);
lean_dec(v_m_1711_);
return v_snap_1710_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1712_);
lean_dec(v_m_1711_);
return v_snap_1710_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1820_, lean_object* v_incr_1821_, lean_object* v_res_1822_){
_start:
{
lean_object* v_cmdState_1824_; lean_object* v_env_1825_; lean_object* v_initModIdxs_1826_; lean_object* v___x_1827_; 
v_cmdState_1824_ = lean_ctor_get(v_res_1822_, 0);
lean_inc_ref(v_cmdState_1824_);
lean_dec_ref(v_res_1822_);
v_env_1825_ = lean_ctor_get(v_cmdState_1824_, 0);
lean_inc_ref(v_env_1825_);
lean_dec_ref(v_cmdState_1824_);
v_initModIdxs_1826_ = lean_ctor_get(v_incr_1821_, 1);
v___x_1827_ = l_Lean_runInitAttrsForModules(v_env_1825_, v_initModIdxs_1826_, v_opts_1820_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1828_, lean_object* v_incr_1829_, lean_object* v_res_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1828_, v_incr_1829_, v_res_1830_);
lean_dec_ref(v_incr_1829_);
lean_dec_ref(v_opts_1828_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_enable_initializer_execution();
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1840_, lean_object* v_incrFile_1841_, lean_object* v_toSave_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v_regions_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1844_ = l_Lean_Environment_header(v_env_1840_);
v_regions_1845_ = lean_ctor_get(v___x_1844_, 2);
lean_inc_ref(v_regions_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1847_ = lean_box(0);
v___x_1848_ = 1;
v___x_1849_ = lean_compacted_region_save(v_incrFile_1841_, v___x_1846_, v_toSave_1842_, v_regions_1845_, v___x_1847_, v___x_1848_);
lean_dec_ref(v_regions_1845_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1850_, lean_object* v_incrFile_1851_, lean_object* v_toSave_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1850_, v_incrFile_1851_, v_toSave_1852_);
lean_dec_ref(v_toSave_1852_);
lean_dec_ref(v_incrFile_1851_);
lean_dec_ref(v_env_1850_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_opts_1855_, lean_object* v_opt_1856_){
_start:
{
lean_object* v_name_1857_; lean_object* v_map_1858_; lean_object* v___x_1859_; 
v_name_1857_ = lean_ctor_get(v_opt_1856_, 0);
v_map_1858_ = lean_ctor_get(v_opts_1855_, 0);
v___x_1859_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1858_, v_name_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_box(0);
return v___x_1860_;
}
else
{
lean_object* v_val_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1870_; 
v_val_1861_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1863_ = v___x_1859_;
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_val_1861_);
lean_dec(v___x_1859_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1870_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
if (lean_obj_tag(v_val_1861_) == 0)
{
lean_object* v_v_1865_; lean_object* v___x_1867_; 
v_v_1865_ = lean_ctor_get(v_val_1861_, 0);
lean_inc_ref(v_v_1865_);
lean_dec_ref_known(v_val_1861_, 1);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_v_1865_);
v___x_1867_ = v___x_1863_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_v_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v___x_1869_; 
lean_del_object(v___x_1863_);
lean_dec(v_val_1861_);
v___x_1869_ = lean_box(0);
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4___boxed(lean_object* v_opts_1871_, lean_object* v_opt_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v_opts_1871_, v_opt_1872_);
lean_dec_ref(v_opt_1872_);
lean_dec_ref(v_opts_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(lean_object* v_opts_1874_, lean_object* v_opt_1875_){
_start:
{
lean_object* v_name_1876_; lean_object* v_defValue_1877_; lean_object* v_map_1878_; lean_object* v___x_1879_; 
v_name_1876_ = lean_ctor_get(v_opt_1875_, 0);
v_defValue_1877_ = lean_ctor_get(v_opt_1875_, 1);
v_map_1878_ = lean_ctor_get(v_opts_1874_, 0);
v___x_1879_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1878_, v_name_1876_);
if (lean_obj_tag(v___x_1879_) == 0)
{
uint8_t v___x_1880_; 
v___x_1880_ = lean_unbox(v_defValue_1877_);
return v___x_1880_;
}
else
{
lean_object* v_val_1881_; 
v_val_1881_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_val_1881_);
lean_dec_ref_known(v___x_1879_, 1);
if (lean_obj_tag(v_val_1881_) == 1)
{
uint8_t v_v_1882_; 
v_v_1882_ = lean_ctor_get_uint8(v_val_1881_, 0);
lean_dec_ref_known(v_val_1881_, 0);
return v_v_1882_;
}
else
{
uint8_t v___x_1883_; 
lean_dec(v_val_1881_);
v___x_1883_ = lean_unbox(v_defValue_1877_);
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_opts_1884_, lean_object* v_opt_1885_){
_start:
{
uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_res_1886_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1884_, v_opt_1885_);
lean_dec_ref(v_opt_1885_);
lean_dec_ref(v_opts_1884_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x1_1888_, lean_object* v_x2_1889_){
_start:
{
lean_object* v_elabSnap_1890_; lean_object* v_resultSnap_1891_; lean_object* v___x_1892_; lean_object* v_codeQualityEntryTasks_1893_; lean_object* v___x_1894_; 
v_elabSnap_1890_ = lean_ctor_get(v_x2_1889_, 3);
lean_inc_ref(v_elabSnap_1890_);
lean_dec_ref(v_x2_1889_);
v_resultSnap_1891_ = lean_ctor_get(v_elabSnap_1890_, 2);
lean_inc_ref(v_resultSnap_1891_);
lean_dec_ref(v_elabSnap_1890_);
v___x_1892_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_1891_);
v_codeQualityEntryTasks_1893_ = lean_ctor_get(v___x_1892_, 2);
lean_inc_ref(v_codeQualityEntryTasks_1893_);
lean_dec(v___x_1892_);
v___x_1894_ = l_Array_append___redArg(v_x1_1888_, v_codeQualityEntryTasks_1893_);
lean_dec_ref(v_codeQualityEntryTasks_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_x_1895_, lean_object* v_x_1896_, lean_object* v_hOpt_1897_){
_start:
{
lean_inc_ref(v_hOpt_1897_);
return v_hOpt_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_x_1898_, lean_object* v_x_1899_, lean_object* v_hOpt_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_Elab_runFrontend___lam__1(v_x_1898_, v_x_1899_, v_hOpt_1900_);
lean_dec_ref(v_hOpt_1900_);
lean_dec_ref(v_x_1899_);
lean_dec(v_x_1898_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(size_t v_sz_1902_, size_t v_i_1903_, lean_object* v_bs_1904_){
_start:
{
uint8_t v___x_1905_; 
v___x_1905_ = lean_usize_dec_lt(v_i_1903_, v_sz_1902_);
if (v___x_1905_ == 0)
{
return v_bs_1904_;
}
else
{
lean_object* v_v_1906_; lean_object* v___x_1907_; lean_object* v_bs_x27_1908_; lean_object* v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; lean_object* v___x_1912_; 
v_v_1906_ = lean_array_uget(v_bs_1904_, v_i_1903_);
v___x_1907_ = lean_unsigned_to_nat(0u);
v_bs_x27_1908_ = lean_array_uset(v_bs_1904_, v_i_1903_, v___x_1907_);
v___x_1909_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1906_);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_add(v_i_1903_, v___x_1910_);
v___x_1912_ = lean_array_uset(v_bs_x27_1908_, v_i_1903_, v___x_1909_);
v_i_1903_ = v___x_1911_;
v_bs_1904_ = v___x_1912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11___boxed(lean_object* v_sz_1914_, lean_object* v_i_1915_, lean_object* v_bs_1916_){
_start:
{
size_t v_sz_boxed_1917_; size_t v_i_boxed_1918_; lean_object* v_res_1919_; 
v_sz_boxed_1917_ = lean_unbox_usize(v_sz_1914_);
lean_dec(v_sz_1914_);
v_i_boxed_1918_ = lean_unbox_usize(v_i_1915_);
lean_dec(v_i_1915_);
v_res_1919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_boxed_1917_, v_i_boxed_1918_, v_bs_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_a_1920_){
_start:
{
size_t v_sz_1921_; size_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v_sz_1921_ = lean_array_size(v_a_1920_);
v___x_1922_ = ((size_t)0ULL);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8_spec__11(v_sz_1921_, v___x_1922_, v_a_1920_);
v___x_1924_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_a_1925_, uint8_t v___x_1926_, lean_object* v_incrFile_1927_, lean_object* v_snapToSave_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v_regions_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1930_ = l_Lean_Environment_header(v_a_1925_);
v_regions_1931_ = lean_ctor_get(v___x_1930_, 2);
lean_inc_ref(v_regions_1931_);
lean_dec_ref(v___x_1930_);
v___x_1932_ = l_Lean_getRegularInitAttrModIdxs(v_a_1925_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_snapToSave_1928_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_compacted_region_save(v_incrFile_1927_, v___x_1934_, v___x_1933_, v_regions_1931_, v___x_1935_, v___x_1926_);
lean_dec_ref_known(v___x_1933_, 2);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref_known(v___x_1936_, 1);
v___x_1938_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1931_);
lean_dec_ref(v_regions_1931_);
v___x_1939_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1940_ = l_System_FilePath_addExtension(v_incrFile_1927_, v___x_1939_);
v___x_1941_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__8(v___x_1938_);
v___x_1942_ = l_Lean_Json_compress(v___x_1941_);
v___x_1943_ = l_IO_FS_writeFile(v___x_1940_, v___x_1942_);
lean_dec_ref(v___x_1942_);
lean_dec_ref(v___x_1940_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1951_; 
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1952_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1951_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_runtime_forget(v_a_1937_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1947_);
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
else
{
lean_dec(v_a_1937_);
return v___x_1943_;
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec_ref(v_regions_1931_);
lean_dec_ref(v_incrFile_1927_);
v_a_1953_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1936_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1936_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_a_1961_, lean_object* v___x_1962_, lean_object* v_incrFile_1963_, lean_object* v_snapToSave_1964_, lean_object* v___y_1965_){
_start:
{
uint8_t v___x_5975__boxed_1966_; lean_object* v_res_1967_; 
v___x_5975__boxed_1966_ = lean_unbox(v___x_1962_);
v_res_1967_ = l_Lean_Elab_runFrontend___lam__2(v_a_1961_, v___x_5975__boxed_1966_, v_incrFile_1963_, v_snapToSave_1964_);
lean_dec_ref(v_a_1961_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_fileMap_1968_, lean_object* v_a_1969_, lean_object* v___x_1970_, lean_object* v_opts_1971_, lean_object* v_val_1972_, uint8_t v___x_1973_, uint8_t v_a_1974_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = l_Lean_Linter_recordLints(v_fileMap_1968_, v_a_1969_, v___x_1970_);
v___x_1977_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1978_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v_opts_1971_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_writeModule(v___x_1976_, v_val_1972_, v___x_1973_);
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_writeModule(v___x_1976_, v_val_1972_, v_a_1974_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_fileMap_1981_, lean_object* v_a_1982_, lean_object* v___x_1983_, lean_object* v_opts_1984_, lean_object* v_val_1985_, lean_object* v___x_1986_, lean_object* v_a_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v___x_6049__boxed_1989_; uint8_t v_a_6050__boxed_1990_; lean_object* v_res_1991_; 
v___x_6049__boxed_1989_ = lean_unbox(v___x_1986_);
v_a_6050__boxed_1990_ = lean_unbox(v_a_1987_);
v_res_1991_ = l_Lean_Elab_runFrontend___lam__3(v_fileMap_1981_, v_a_1982_, v___x_1983_, v_opts_1984_, v_val_1985_, v___x_6049__boxed_1989_, v_a_6050__boxed_1990_);
lean_dec_ref(v_opts_1984_);
lean_dec_ref(v___x_1983_);
lean_dec_ref(v_fileMap_1981_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1992_, size_t v_i_1993_, size_t v_stop_1994_, lean_object* v_b_1995_){
_start:
{
uint8_t v___x_1997_; 
v___x_1997_ = lean_usize_dec_eq(v_i_1993_, v_stop_1994_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = lean_array_uget_borrowed(v_as_1992_, v_i_1993_);
lean_inc(v___x_1998_);
v___x_1999_ = lean_load_dynlib(v___x_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; size_t v___x_2001_; size_t v___x_2002_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___x_2001_ = ((size_t)1ULL);
v___x_2002_ = lean_usize_add(v_i_1993_, v___x_2001_);
v_i_1993_ = v___x_2002_;
v_b_1995_ = v_a_2000_;
goto _start;
}
else
{
return v___x_1999_;
}
}
else
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_b_1995_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_2005_, lean_object* v_i_2006_, lean_object* v_stop_2007_, lean_object* v_b_2008_, lean_object* v___y_2009_){
_start:
{
size_t v_i_boxed_2010_; size_t v_stop_boxed_2011_; lean_object* v_res_2012_; 
v_i_boxed_2010_ = lean_unbox_usize(v_i_2006_);
lean_dec(v_i_2006_);
v_stop_boxed_2011_ = lean_unbox_usize(v_stop_2007_);
lean_dec(v_stop_2007_);
v_res_2012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_2005_, v_i_boxed_2010_, v_stop_boxed_2011_, v_b_2008_);
lean_dec_ref(v_as_2005_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_setup_x3f_2013_, lean_object* v___f_2014_, lean_object* v___x_2015_, lean_object* v_plugins_2016_, uint32_t v_trustLevel_2017_, uint8_t v___x_2018_, lean_object* v_mainModuleName_2019_, lean_object* v_stx_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; uint8_t v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; 
if (lean_obj_tag(v_setup_x3f_2013_) == 1)
{
lean_object* v_val_2037_; lean_object* v_name_2038_; lean_object* v_package_x3f_2039_; uint8_t v_isModule_2040_; lean_object* v_imports_x3f_2041_; lean_object* v_importArts_2042_; lean_object* v_dynlibs_2043_; lean_object* v_plugins_2044_; lean_object* v_options_2045_; lean_object* v___y_2052_; lean_object* v___x_2061_; lean_object* v___x_2062_; uint8_t v___x_2063_; 
lean_dec(v_mainModuleName_2019_);
v_val_2037_ = lean_ctor_get(v_setup_x3f_2013_, 0);
lean_inc(v_val_2037_);
lean_dec_ref_known(v_setup_x3f_2013_, 1);
v_name_2038_ = lean_ctor_get(v_val_2037_, 0);
lean_inc(v_name_2038_);
v_package_x3f_2039_ = lean_ctor_get(v_val_2037_, 1);
lean_inc(v_package_x3f_2039_);
v_isModule_2040_ = lean_ctor_get_uint8(v_val_2037_, sizeof(void*)*7);
v_imports_x3f_2041_ = lean_ctor_get(v_val_2037_, 2);
lean_inc(v_imports_x3f_2041_);
v_importArts_2042_ = lean_ctor_get(v_val_2037_, 3);
lean_inc(v_importArts_2042_);
v_dynlibs_2043_ = lean_ctor_get(v_val_2037_, 4);
lean_inc_ref(v_dynlibs_2043_);
v_plugins_2044_ = lean_ctor_get(v_val_2037_, 5);
lean_inc_ref(v_plugins_2044_);
v_options_2045_ = lean_ctor_get(v_val_2037_, 6);
lean_inc(v_options_2045_);
lean_dec(v_val_2037_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v___x_2062_ = lean_array_get_size(v_dynlibs_2043_);
v___x_2063_ = lean_nat_dec_lt(v___x_2061_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_dec_ref(v_dynlibs_2043_);
goto v___jp_2046_;
}
else
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = lean_box(0);
v___x_2065_ = lean_nat_dec_le(v___x_2062_, v___x_2062_);
if (v___x_2065_ == 0)
{
if (v___x_2063_ == 0)
{
lean_dec_ref(v_dynlibs_2043_);
goto v___jp_2046_;
}
else
{
size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = lean_usize_of_nat(v___x_2062_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2043_, v___x_2066_, v___x_2067_, v___x_2064_);
lean_dec_ref(v_dynlibs_2043_);
v___y_2052_ = v___x_2068_;
goto v___jp_2051_;
}
}
else
{
size_t v___x_2069_; size_t v___x_2070_; lean_object* v___x_2071_; 
v___x_2069_ = ((size_t)0ULL);
v___x_2070_ = lean_usize_of_nat(v___x_2062_);
v___x_2071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2043_, v___x_2069_, v___x_2070_, v___x_2064_);
lean_dec_ref(v_dynlibs_2043_);
v___y_2052_ = v___x_2071_;
goto v___jp_2051_;
}
}
v___jp_2046_:
{
uint8_t v___x_2047_; uint8_t v___x_2048_; 
v___x_2047_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2020_);
v___x_2048_ = lean_strict_or(v_isModule_2040_, v___x_2047_);
if (lean_obj_tag(v_imports_x3f_2041_) == 0)
{
lean_object* v___x_2049_; 
v___x_2049_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2020_, v___x_2018_);
v___y_2024_ = v_options_2045_;
v___y_2025_ = v_name_2038_;
v___y_2026_ = v_package_x3f_2039_;
v___y_2027_ = v_plugins_2044_;
v___y_2028_ = v___x_2048_;
v___y_2029_ = v_importArts_2042_;
v___y_2030_ = v___x_2049_;
goto v___jp_2023_;
}
else
{
lean_object* v_val_2050_; 
lean_dec(v_stx_2020_);
v_val_2050_ = lean_ctor_get(v_imports_x3f_2041_, 0);
lean_inc(v_val_2050_);
lean_dec_ref_known(v_imports_x3f_2041_, 1);
v___y_2024_ = v_options_2045_;
v___y_2025_ = v_name_2038_;
v___y_2026_ = v_package_x3f_2039_;
v___y_2027_ = v_plugins_2044_;
v___y_2028_ = v___x_2048_;
v___y_2029_ = v_importArts_2042_;
v___y_2030_ = v_val_2050_;
goto v___jp_2023_;
}
}
v___jp_2051_:
{
if (lean_obj_tag(v___y_2052_) == 0)
{
lean_dec_ref_known(v___y_2052_, 1);
goto v___jp_2046_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_options_2045_);
lean_dec_ref(v_plugins_2044_);
lean_dec(v_importArts_2042_);
lean_dec(v_imports_x3f_2041_);
lean_dec(v_package_x3f_2039_);
lean_dec(v_name_2038_);
lean_dec(v_stx_2020_);
lean_dec_ref(v_plugins_2016_);
lean_dec_ref(v___x_2015_);
lean_dec_ref(v___f_2014_);
v_a_2053_ = lean_ctor_get(v___y_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___y_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___y_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___y_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
else
{
lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref(v___f_2014_);
lean_dec(v_setup_x3f_2013_);
v___x_2072_ = lean_box(0);
v___x_2073_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2020_);
v___x_2074_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2020_, v___x_2018_);
v___x_2075_ = lean_box(1);
v___x_2076_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2076_, 0, v_mainModuleName_2019_);
lean_ctor_set(v___x_2076_, 1, v___x_2072_);
lean_ctor_set(v___x_2076_, 2, v___x_2074_);
lean_ctor_set(v___x_2076_, 3, v___x_2015_);
lean_ctor_set(v___x_2076_, 4, v___x_2075_);
lean_ctor_set(v___x_2076_, 5, v_plugins_2016_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*6 + 4, v___x_2073_);
lean_ctor_set_uint32(v___x_2076_, sizeof(void*)*6, v_trustLevel_2017_);
v___x_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
v___jp_2023_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2031_ = l_Lean_LeanOptions_toOptions(v___y_2024_);
v___x_2032_ = l_Lean_Options_mergeBy(v___f_2014_, v___x_2015_, v___x_2031_);
v___x_2033_ = l_Array_append___redArg(v_plugins_2016_, v___y_2027_);
lean_dec_ref(v___y_2027_);
v___x_2034_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2034_, 0, v___y_2025_);
lean_ctor_set(v___x_2034_, 1, v___y_2026_);
lean_ctor_set(v___x_2034_, 2, v___y_2030_);
lean_ctor_set(v___x_2034_, 3, v___x_2032_);
lean_ctor_set(v___x_2034_, 4, v___y_2029_);
lean_ctor_set(v___x_2034_, 5, v___x_2033_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*6 + 4, v___y_2028_);
lean_ctor_set_uint32(v___x_2034_, sizeof(void*)*6, v_trustLevel_2017_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_setup_x3f_2079_, lean_object* v___f_2080_, lean_object* v___x_2081_, lean_object* v_plugins_2082_, lean_object* v_trustLevel_2083_, lean_object* v___x_2084_, lean_object* v_mainModuleName_2085_, lean_object* v_stx_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint32_t v_trustLevel_boxed_2089_; uint8_t v___x_6096__boxed_2090_; lean_object* v_res_2091_; 
v_trustLevel_boxed_2089_ = lean_unbox_uint32(v_trustLevel_2083_);
lean_dec(v_trustLevel_2083_);
v___x_6096__boxed_2090_ = lean_unbox(v___x_2084_);
v_res_2091_ = l_Lean_Elab_runFrontend___lam__4(v_setup_x3f_2079_, v___f_2080_, v___x_2081_, v_plugins_2082_, v_trustLevel_boxed_2089_, v___x_6096__boxed_2090_, v_mainModuleName_2085_, v_stx_2086_, v___y_2087_);
lean_dec_ref(v___y_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5(lean_object* v_val_2092_, lean_object* v_initModIdxs_2093_, lean_object* v___x_2094_){
_start:
{
lean_object* v_cmdState_2096_; lean_object* v_env_2097_; lean_object* v___x_2098_; 
v_cmdState_2096_ = lean_ctor_get(v_val_2092_, 0);
lean_inc_ref(v_cmdState_2096_);
lean_dec_ref(v_val_2092_);
v_env_2097_ = lean_ctor_get(v_cmdState_2096_, 0);
lean_inc_ref(v_env_2097_);
lean_dec_ref(v_cmdState_2096_);
v___x_2098_ = l_Lean_runInitAttrsForModules(v_env_2097_, v_initModIdxs_2093_, v___x_2094_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__5___boxed(lean_object* v_val_2099_, lean_object* v_initModIdxs_2100_, lean_object* v___x_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_Elab_runFrontend___lam__5(v_val_2099_, v_initModIdxs_2100_, v___x_2101_);
lean_dec_ref(v___x_2101_);
lean_dec_ref(v_initModIdxs_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(size_t v_sz_2104_, size_t v_i_2105_, lean_object* v_bs_2106_){
_start:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_usize_dec_lt(v_i_2105_, v_sz_2104_);
if (v___x_2107_ == 0)
{
return v_bs_2106_;
}
else
{
lean_object* v_v_2108_; lean_object* v_traces_2109_; lean_object* v___x_2110_; lean_object* v_bs_x27_2111_; size_t v___x_2112_; size_t v___x_2113_; lean_object* v___x_2114_; 
v_v_2108_ = lean_array_uget_borrowed(v_bs_2106_, v_i_2105_);
v_traces_2109_ = lean_ctor_get(v_v_2108_, 3);
lean_inc_ref(v_traces_2109_);
v___x_2110_ = lean_unsigned_to_nat(0u);
v_bs_x27_2111_ = lean_array_uset(v_bs_2106_, v_i_2105_, v___x_2110_);
v___x_2112_ = ((size_t)1ULL);
v___x_2113_ = lean_usize_add(v_i_2105_, v___x_2112_);
v___x_2114_ = lean_array_uset(v_bs_x27_2111_, v_i_2105_, v_traces_2109_);
v_i_2105_ = v___x_2113_;
v_bs_2106_ = v___x_2114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_sz_2116_, lean_object* v_i_2117_, lean_object* v_bs_2118_){
_start:
{
size_t v_sz_boxed_2119_; size_t v_i_boxed_2120_; lean_object* v_res_2121_; 
v_sz_boxed_2119_ = lean_unbox_usize(v_sz_2116_);
lean_dec(v_sz_2116_);
v_i_boxed_2120_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_res_2121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_boxed_2119_, v_i_boxed_2120_, v_bs_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_as_2122_, size_t v_i_2123_, size_t v_stop_2124_, lean_object* v_b_2125_){
_start:
{
lean_object* v___y_2127_; uint8_t v___x_2131_; 
v___x_2131_ = lean_usize_dec_eq(v_i_2123_, v_stop_2124_);
if (v___x_2131_ == 0)
{
lean_object* v___x_2132_; lean_object* v_infoTree_x3f_2133_; 
v___x_2132_ = lean_array_uget_borrowed(v_as_2122_, v_i_2123_);
v_infoTree_x3f_2133_ = lean_ctor_get(v___x_2132_, 2);
if (lean_obj_tag(v_infoTree_x3f_2133_) == 1)
{
lean_object* v_val_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v_val_2134_ = lean_ctor_get(v_infoTree_x3f_2133_, 0);
v___x_2135_ = lean_unsigned_to_nat(1u);
v___x_2136_ = lean_mk_empty_array_with_capacity(v___x_2135_);
lean_inc(v_val_2134_);
v___x_2137_ = lean_array_push(v___x_2136_, v_val_2134_);
v___x_2138_ = l_Array_append___redArg(v_b_2125_, v___x_2137_);
lean_dec_ref(v___x_2137_);
v___y_2127_ = v___x_2138_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2140_ = l_Array_append___redArg(v_b_2125_, v___x_2139_);
v___y_2127_ = v___x_2140_;
goto v___jp_2126_;
}
}
else
{
return v_b_2125_;
}
v___jp_2126_:
{
size_t v___x_2128_; size_t v___x_2129_; 
v___x_2128_ = ((size_t)1ULL);
v___x_2129_ = lean_usize_add(v_i_2123_, v___x_2128_);
v_i_2123_ = v___x_2129_;
v_b_2125_ = v___y_2127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_as_2141_, lean_object* v_i_2142_, lean_object* v_stop_2143_, lean_object* v_b_2144_){
_start:
{
size_t v_i_boxed_2145_; size_t v_stop_boxed_2146_; lean_object* v_res_2147_; 
v_i_boxed_2145_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_stop_boxed_2146_ = lean_unbox_usize(v_stop_2143_);
lean_dec(v_stop_2143_);
v_res_2147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v_as_2141_, v_i_boxed_2145_, v_stop_boxed_2146_, v_b_2144_);
lean_dec_ref(v_as_2141_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(lean_object* v_as_2148_, size_t v_i_2149_, size_t v_stop_2150_, lean_object* v_b_2151_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_eq(v_i_2149_, v_stop_2150_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; size_t v___x_2157_; size_t v___x_2158_; 
v___x_2153_ = lean_array_uget_borrowed(v_as_2148_, v_i_2149_);
v___x_2154_ = 2;
v___x_2155_ = lean_box(v___x_2154_);
lean_inc(v___x_2153_);
v___x_2156_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2153_, v___x_2155_, v_b_2151_);
v___x_2157_ = ((size_t)1ULL);
v___x_2158_ = lean_usize_add(v_i_2149_, v___x_2157_);
v_i_2149_ = v___x_2158_;
v_b_2151_ = v___x_2156_;
goto _start;
}
else
{
return v_b_2151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9___boxed(lean_object* v_as_2160_, lean_object* v_i_2161_, lean_object* v_stop_2162_, lean_object* v_b_2163_){
_start:
{
size_t v_i_boxed_2164_; size_t v_stop_boxed_2165_; lean_object* v_res_2166_; 
v_i_boxed_2164_ = lean_unbox_usize(v_i_2161_);
lean_dec(v_i_2161_);
v_stop_boxed_2165_ = lean_unbox_usize(v_stop_2162_);
lean_dec(v_stop_2162_);
v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_as_2160_, v_i_boxed_2164_, v_stop_boxed_2165_, v_b_2163_);
lean_dec_ref(v_as_2160_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2170_, lean_object* v_k_2171_, uint8_t v_v_2172_){
_start:
{
lean_object* v_map_2173_; uint8_t v_hasTrace_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2188_; 
v_map_2173_ = lean_ctor_get(v_o_2170_, 0);
v_hasTrace_2174_ = lean_ctor_get_uint8(v_o_2170_, sizeof(void*)*1);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_o_2170_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2176_ = v_o_2170_;
v_isShared_2177_ = v_isSharedCheck_2188_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_map_2173_);
lean_dec(v_o_2170_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2188_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2178_, 0, v_v_2172_);
lean_inc(v_k_2171_);
v___x_2179_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2171_, v___x_2178_, v_map_2173_);
if (v_hasTrace_2174_ == 0)
{
lean_object* v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2181_ = l_Lean_Name_isPrefixOf(v___x_2180_, v_k_2171_);
lean_dec(v_k_2171_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2179_);
v___x_2183_ = v___x_2176_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2179_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*1, v___x_2181_);
return v___x_2183_;
}
}
else
{
lean_object* v___x_2186_; 
lean_dec(v_k_2171_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2179_);
v___x_2186_ = v___x_2176_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2187_, sizeof(void*)*1, v_hasTrace_2174_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2189_, lean_object* v_k_2190_, lean_object* v_v_2191_){
_start:
{
uint8_t v_v_boxed_2192_; lean_object* v_res_2193_; 
v_v_boxed_2192_ = lean_unbox(v_v_2191_);
v_res_2193_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2189_, v_k_2190_, v_v_boxed_2192_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2194_, lean_object* v_opt_2195_, uint8_t v_val_2196_){
_start:
{
lean_object* v_name_2197_; lean_object* v___x_2198_; 
v_name_2197_ = lean_ctor_get(v_opt_2195_, 0);
lean_inc(v_name_2197_);
lean_dec_ref(v_opt_2195_);
v___x_2198_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2194_, v_name_2197_, v_val_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2199_, lean_object* v_opt_2200_, lean_object* v_val_2201_){
_start:
{
uint8_t v_val_boxed_2202_; lean_object* v_res_2203_; 
v_val_boxed_2202_ = lean_unbox(v_val_2201_);
v_res_2203_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2199_, v_opt_2200_, v_val_boxed_2202_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2204_, lean_object* v_opt_2205_, uint8_t v_val_2206_){
_start:
{
lean_object* v_name_2207_; lean_object* v_map_2208_; uint8_t v___x_2209_; 
v_name_2207_ = lean_ctor_get(v_opt_2205_, 0);
v_map_2208_ = lean_ctor_get(v_opts_2204_, 0);
v___x_2209_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2207_, v_map_2208_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; 
v___x_2210_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2204_, v_opt_2205_, v_val_2206_);
return v___x_2210_;
}
else
{
lean_dec_ref(v_opt_2205_);
return v_opts_2204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2211_, lean_object* v_opt_2212_, lean_object* v_val_2213_){
_start:
{
uint8_t v_val_boxed_2214_; lean_object* v_res_2215_; 
v_val_boxed_2214_ = lean_unbox(v_val_2213_);
v_res_2215_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2211_, v_opt_2212_, v_val_boxed_2214_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0(lean_object* v_a_2216_, lean_object* v_entries_2217_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_task_get_own(v_a_2216_);
v___x_2219_ = l_Array_append___redArg(v_entries_2217_, v___x_2218_);
lean_dec(v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_as_2220_, size_t v_sz_2221_, size_t v_i_2222_, lean_object* v_b_2223_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_usize_dec_lt(v_i_2222_, v_sz_2221_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_b_2223_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; lean_object* v_toEnvExtension_2228_; lean_object* v_asyncMode_2229_; lean_object* v_a_2230_; lean_object* v___f_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; size_t v___x_2234_; size_t v___x_2235_; 
v___x_2227_ = l_Lean_Linter_codeQualityLogExt;
v_toEnvExtension_2228_ = lean_ctor_get(v___x_2227_, 0);
v_asyncMode_2229_ = lean_ctor_get(v_toEnvExtension_2228_, 2);
v_a_2230_ = lean_array_uget_borrowed(v_as_2220_, v_i_2222_);
lean_inc(v_a_2230_);
v___f_2231_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2231_, 0, v_a_2230_);
v___x_2232_ = lean_box(0);
v___x_2233_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_2227_, v_b_2223_, v___f_2231_, v_asyncMode_2229_, v___x_2232_);
v___x_2234_ = ((size_t)1ULL);
v___x_2235_ = lean_usize_add(v_i_2222_, v___x_2234_);
v_i_2222_ = v___x_2235_;
v_b_2223_ = v___x_2233_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_as_2237_, lean_object* v_sz_2238_, lean_object* v_i_2239_, lean_object* v_b_2240_, lean_object* v___y_2241_){
_start:
{
size_t v_sz_boxed_2242_; size_t v_i_boxed_2243_; lean_object* v_res_2244_; 
v_sz_boxed_2242_ = lean_unbox_usize(v_sz_2238_);
lean_dec(v_sz_2238_);
v_i_boxed_2243_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_as_2237_, v_sz_boxed_2242_, v_i_boxed_2243_, v_b_2240_);
lean_dec_ref(v_as_2237_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = l_Lean_Language_Snapshot_transform(v_s_2247_, v___y_2248_);
v___x_2250_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2249_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2252_, v___y_2253_);
lean_dec_ref(v___y_2253_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v___f_2258_; lean_object* v___x_2259_; 
v___f_2258_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2259_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2256_, v___f_2258_, v_a_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2260_, v_a_2261_);
lean_dec_ref(v_a_2261_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2267_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2264_, v___x_2266_, v_a_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2268_, v_a_2269_);
lean_dec_ref(v_a_2269_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_toSnapshot_2273_; lean_object* v_metaSnap_2274_; lean_object* v_result_x3f_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___y_2279_; 
v_toSnapshot_2273_ = lean_ctor_get(v_s_2271_, 0);
lean_inc_ref(v_toSnapshot_2273_);
v_metaSnap_2274_ = lean_ctor_get(v_s_2271_, 1);
lean_inc_ref(v_metaSnap_2274_);
v_result_x3f_2275_ = lean_ctor_get(v_s_2271_, 2);
lean_inc(v_result_x3f_2275_);
lean_dec_ref(v_s_2271_);
v___x_2276_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2273_, v___y_2272_);
v___x_2277_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2274_, v___y_2272_);
if (lean_obj_tag(v_result_x3f_2275_) == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_box(0);
v___y_2279_ = v___x_2285_;
goto v___jp_2278_;
}
else
{
lean_object* v_val_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2295_; 
v_val_2286_ = lean_ctor_get(v_result_x3f_2275_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_result_x3f_2275_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2288_ = v_result_x3f_2275_;
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_val_2286_);
lean_dec(v_result_x3f_2275_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2295_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_firstCmdSnap_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v_firstCmdSnap_2290_ = lean_ctor_get(v_val_2286_, 1);
lean_inc_ref(v_firstCmdSnap_2290_);
lean_dec(v_val_2286_);
v___x_2291_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2290_, v___y_2272_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 0, v___x_2291_);
v___x_2293_ = v___x_2288_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
v___y_2279_ = v___x_2293_;
goto v___jp_2278_;
}
}
}
v___jp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_mk_empty_array_with_capacity(v___x_2280_);
v___x_2282_ = lean_array_push(v___x_2281_, v___x_2277_);
v___x_2283_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2279_, v___x_2282_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2276_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2296_, v___y_2297_);
lean_dec_ref(v___y_2297_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___f_2302_; lean_object* v___x_2303_; 
v___f_2302_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2303_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2300_, v___f_2302_, v_a_2301_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2304_, v_a_2305_);
lean_dec_ref(v_a_2305_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2307_){
_start:
{
lean_object* v_toSnapshot_2308_; lean_object* v_metaSnap_2309_; lean_object* v_result_x3f_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___y_2315_; 
v_toSnapshot_2308_ = lean_ctor_get(v_a_2307_, 0);
lean_inc_ref(v_toSnapshot_2308_);
v_metaSnap_2309_ = lean_ctor_get(v_a_2307_, 1);
lean_inc_ref(v_metaSnap_2309_);
v_result_x3f_2310_ = lean_ctor_get(v_a_2307_, 4);
lean_inc(v_result_x3f_2310_);
lean_dec_ref(v_a_2307_);
v___x_2311_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2312_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2308_, v___x_2311_);
v___x_2313_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2309_, v___x_2311_);
if (lean_obj_tag(v_result_x3f_2310_) == 0)
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_box(0);
v___y_2315_ = v___x_2321_;
goto v___jp_2314_;
}
else
{
lean_object* v_val_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2331_; 
v_val_2322_ = lean_ctor_get(v_result_x3f_2310_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_result_x3f_2310_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2324_ = v_result_x3f_2310_;
v_isShared_2325_ = v_isSharedCheck_2331_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_val_2322_);
lean_dec(v_result_x3f_2310_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2331_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v_processedSnap_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v_processedSnap_2326_ = lean_ctor_get(v_val_2322_, 1);
lean_inc_ref(v_processedSnap_2326_);
lean_dec(v_val_2322_);
v___x_2327_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2326_, v___x_2311_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2327_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
v___y_2315_ = v___x_2329_;
goto v___jp_2314_;
}
}
}
v___jp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2316_ = lean_unsigned_to_nat(1u);
v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
v___x_2318_ = lean_array_push(v___x_2317_, v___x_2313_);
v___x_2319_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2315_, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2312_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
return v___x_2320_;
}
}
}
static double _init_l_Lean_Elab_runFrontend___closed__2(void){
_start:
{
lean_object* v___x_2334_; double v___x_2335_; 
v___x_2334_ = lean_unsigned_to_nat(1000000000u);
v___x_2335_ = lean_float_of_nat(v___x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2337_, lean_object* v_opts_2338_, lean_object* v_fileName_2339_, lean_object* v_mainModuleName_2340_, uint32_t v_trustLevel_2341_, lean_object* v_oleanFileName_x3f_2342_, lean_object* v_ileanFileName_x3f_2343_, uint8_t v_jsonOutput_2344_, lean_object* v_errorOnKinds_2345_, lean_object* v_plugins_2346_, uint8_t v_printStats_2347_, lean_object* v_setup_x3f_2348_, lean_object* v_incrSaveFileName_x3f_2349_, lean_object* v_incrLoadFileName_x3f_2350_, lean_object* v_incrHeaderSaveFileName_x3f_2351_){
_start:
{
lean_object* v___y_2354_; lean_object* v___y_2355_; lean_object* v___f_2359_; lean_object* v___f_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; double v___x_2363_; double v___x_2364_; double v___x_2365_; uint8_t v___x_2366_; lean_object* v___y_2368_; lean_object* v___y_2369_; size_t v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; uint8_t v___y_2434_; lean_object* v___y_2435_; size_t v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2471_; lean_object* v___y_2472_; uint8_t v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; size_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2487_; uint8_t v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; uint8_t v___y_2492_; lean_object* v___y_2493_; size_t v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; uint8_t v___y_2525_; lean_object* v___y_2526_; lean_object* v___y_2527_; size_t v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2541_; uint8_t v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; uint8_t v___y_2547_; lean_object* v___y_2548_; size_t v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v_a_2638_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v_a_2655_; lean_object* v___x_2657_; uint8_t v___y_2659_; 
v___f_2359_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___f_2360_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__1));
v___x_2361_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2362_ = lean_io_mono_nanos_now();
v___x_2363_ = lean_float_of_nat(v___x_2362_);
v___x_2364_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__2, &l_Lean_Elab_runFrontend___closed__2_once, _init_l_Lean_Elab_runFrontend___closed__2);
v___x_2365_ = lean_float_div(v___x_2363_, v___x_2364_);
v___x_2366_ = 1;
v___x_2428_ = lean_string_utf8_byte_size(v_input_2337_);
v___x_2429_ = l_Lean_Parser_mkInputContext___redArg(v_input_2337_, v_fileName_2339_, v___x_2366_, v___x_2428_);
v___x_2657_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2349_) == 0)
{
v___y_2659_ = v___x_2366_;
goto v___jp_2658_;
}
else
{
uint8_t v___x_2695_; 
v___x_2695_ = 0;
v___y_2659_ = v___x_2695_;
goto v___jp_2658_;
}
v___jp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = lean_runtime_forget(v___y_2354_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___y_2355_);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
v___jp_2367_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = l_Lean_trace_profiler_output;
v___x_2374_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__4(v___y_2372_, v___x_2373_);
if (lean_obj_tag(v___x_2374_) == 1)
{
lean_object* v_val_2375_; lean_object* v___x_2376_; size_t v_sz_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec_ref(v___y_2369_);
v_val_2375_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_val_2375_);
lean_dec_ref_known(v___x_2374_, 1);
lean_inc_ref(v___y_2368_);
v___x_2376_ = l_Lean_Language_SnapshotTree_getAll(v___y_2368_);
v_sz_2377_ = lean_array_size(v___x_2376_);
v___x_2378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2377_, v___y_2370_, v___x_2376_);
v___x_2379_ = l_Lean_Name_toString(v_mainModuleName_2340_, v___x_2366_);
v___x_2380_ = l_Lean_Firefox_Profile_export(v___x_2379_, v___x_2365_, v___x_2378_, v___y_2372_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___x_2378_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2381_);
v___x_2383_ = l_Lean_Json_compress(v___x_2382_);
v___x_2384_ = l_IO_FS_writeFile(v_val_2375_, v___x_2383_);
lean_dec_ref(v___x_2383_);
lean_dec(v_val_2375_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_dec_ref_known(v___x_2384_, 1);
v___y_2354_ = v___y_2368_;
v___y_2355_ = v___y_2371_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2368_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v_val_2375_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2368_);
v_a_2393_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2380_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2380_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
else
{
lean_object* v___x_2401_; uint8_t v___x_2402_; 
lean_dec(v___x_2374_);
v___x_2401_ = l_Lean_trace_profiler_serve;
v___x_2402_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__6(v___y_2369_, v___x_2401_);
lean_dec_ref(v___y_2369_);
if (v___x_2402_ == 0)
{
lean_dec_ref(v___y_2372_);
lean_dec(v_mainModuleName_2340_);
v___y_2354_ = v___y_2368_;
v___y_2355_ = v___y_2371_;
goto v___jp_2353_;
}
else
{
lean_object* v___x_2403_; size_t v_sz_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_inc_ref(v___y_2368_);
v___x_2403_ = l_Lean_Language_SnapshotTree_getAll(v___y_2368_);
v_sz_2404_ = lean_array_size(v___x_2403_);
v___x_2405_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__5(v_sz_2404_, v___y_2370_, v___x_2403_);
v___x_2406_ = l_Lean_Name_toString(v_mainModuleName_2340_, v___x_2366_);
v___x_2407_ = l_Lean_Firefox_Profile_export(v___x_2406_, v___x_2365_, v___x_2405_, v___y_2372_);
lean_dec_ref(v___y_2372_);
lean_dec_ref(v___x_2405_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2408_);
v___x_2410_ = l_Lean_Json_compress(v___x_2409_);
v___x_2411_ = l_Lean_Firefox_Profile_serve(v___x_2410_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_dec_ref_known(v___x_2411_, 1);
v___y_2354_ = v___y_2368_;
v___y_2355_ = v___y_2371_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2368_);
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec_ref(v___y_2371_);
lean_dec_ref(v___y_2368_);
v_a_2420_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2407_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2407_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
}
}
v___jp_2430_:
{
lean_object* v_fileMap_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_fst_2443_; lean_object* v_snd_2444_; lean_object* v_stx_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2465_; 
v_fileMap_2440_ = lean_ctor_get(v___x_2429_, 2);
lean_inc_ref(v_fileMap_2440_);
lean_dec_ref(v___x_2429_);
v___x_2441_ = l_Lean_Server_findModuleRefs(v_fileMap_2440_, v___y_2439_, v___y_2434_, v___y_2434_);
lean_dec_ref(v___y_2439_);
v___x_2442_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2441_);
v_fst_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_fst_2443_);
v_snd_2444_ = lean_ctor_get(v___x_2442_, 1);
lean_inc(v_snd_2444_);
lean_dec_ref(v___x_2442_);
v_stx_2445_ = lean_ctor_get(v___y_2435_, 3);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___y_2435_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; lean_object* v_unused_2467_; lean_object* v_unused_2468_; lean_object* v_unused_2469_; 
v_unused_2466_ = lean_ctor_get(v___y_2435_, 4);
lean_dec(v_unused_2466_);
v_unused_2467_ = lean_ctor_get(v___y_2435_, 2);
lean_dec(v_unused_2467_);
v_unused_2468_ = lean_ctor_get(v___y_2435_, 1);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v___y_2435_, 0);
lean_dec(v_unused_2469_);
v___x_2447_ = v___y_2435_;
v_isShared_2448_ = v_isSharedCheck_2465_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_stx_2445_);
lean_dec(v___y_2435_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2465_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2449_ = lean_unsigned_to_nat(5u);
v___x_2450_ = l_Lean_Server_collectImports(v_stx_2445_);
lean_inc(v_mainModuleName_2340_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 4, v_snd_2444_);
lean_ctor_set(v___x_2447_, 3, v_fst_2443_);
lean_ctor_set(v___x_2447_, 2, v___x_2450_);
lean_ctor_set(v___x_2447_, 1, v_mainModuleName_2340_);
lean_ctor_set(v___x_2447_, 0, v___x_2449_);
v___x_2452_ = v___x_2447_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_mainModuleName_2340_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2464_, 3, v_fst_2443_);
lean_ctor_set(v_reuseFailAlloc_2464_, 4, v_snd_2444_);
v___x_2452_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2452_);
v___x_2454_ = l_Lean_Json_compress(v___x_2453_);
v___x_2455_ = l_IO_FS_writeFile(v___y_2433_, v___x_2454_);
lean_dec_ref(v___x_2454_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_dec_ref_known(v___x_2455_, 1);
v___y_2368_ = v___y_2431_;
v___y_2369_ = v___y_2432_;
v___y_2370_ = v___y_2436_;
v___y_2371_ = v___y_2437_;
v___y_2372_ = v___y_2438_;
goto v___jp_2367_;
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec_ref(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec_ref(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v_mainModuleName_2340_);
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2455_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
}
v___jp_2470_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2343_) == 1)
{
lean_object* v_val_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v_val_2479_ = lean_ctor_get(v_ileanFileName_x3f_2343_, 0);
lean_inc_ref(v___y_2471_);
v___x_2480_ = l_Lean_Language_SnapshotTree_getAll(v___y_2471_);
v___x_2481_ = lean_mk_empty_array_with_capacity(v___y_2475_);
v___x_2482_ = lean_array_get_size(v___x_2480_);
v___x_2483_ = lean_nat_dec_lt(v___y_2475_, v___x_2482_);
lean_dec(v___y_2475_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v___x_2480_);
v___y_2431_ = v___y_2471_;
v___y_2432_ = v___y_2472_;
v___y_2433_ = v_val_2479_;
v___y_2434_ = v___y_2473_;
v___y_2435_ = v___y_2474_;
v___y_2436_ = v___y_2476_;
v___y_2437_ = v___y_2477_;
v___y_2438_ = v___y_2478_;
v___y_2439_ = v___x_2481_;
goto v___jp_2430_;
}
else
{
size_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_usize_of_nat(v___x_2482_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__7(v___x_2480_, v___y_2476_, v___x_2484_, v___x_2481_);
lean_dec_ref(v___x_2480_);
v___y_2431_ = v___y_2471_;
v___y_2432_ = v___y_2472_;
v___y_2433_ = v_val_2479_;
v___y_2434_ = v___y_2473_;
v___y_2435_ = v___y_2474_;
v___y_2436_ = v___y_2476_;
v___y_2437_ = v___y_2477_;
v___y_2438_ = v___y_2478_;
v___y_2439_ = v___x_2485_;
goto v___jp_2430_;
}
}
else
{
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___x_2429_);
v___y_2368_ = v___y_2471_;
v___y_2369_ = v___y_2472_;
v___y_2370_ = v___y_2476_;
v___y_2371_ = v___y_2477_;
v___y_2372_ = v___y_2478_;
goto v___jp_2367_;
}
}
v___jp_2486_:
{
if (v___y_2492_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2342_) == 1)
{
lean_object* v_val_2498_; lean_object* v_fileMap_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v_val_2498_ = lean_ctor_get(v_oleanFileName_x3f_2342_, 0);
lean_inc(v_val_2498_);
lean_dec_ref_known(v_oleanFileName_x3f_2342_, 1);
v_fileMap_2499_ = lean_ctor_get(v___x_2429_, 2);
lean_inc_ref(v_fileMap_2499_);
v___x_2500_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__3));
v___x_2501_ = lean_box(0);
v___x_2502_ = lean_mk_empty_array_with_capacity(v___y_2495_);
lean_inc_ref(v___y_2490_);
v___x_2503_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2490_, v___x_2501_, v___x_2502_);
v___x_2504_ = lean_box(v___x_2366_);
v___x_2505_ = lean_box(v___y_2488_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2506_, 0, v_fileMap_2499_);
lean_closure_set(v___f_2506_, 1, v___y_2489_);
lean_closure_set(v___f_2506_, 2, v___x_2503_);
lean_closure_set(v___f_2506_, 3, v___y_2487_);
lean_closure_set(v___f_2506_, 4, v_val_2498_);
lean_closure_set(v___f_2506_, 5, v___x_2504_);
lean_closure_set(v___f_2506_, 6, v___x_2505_);
v___x_2507_ = lean_box(0);
v___x_2508_ = l_Lean_profileitIOUnsafe___redArg(v___x_2500_, v___y_2491_, v___f_2506_, v___x_2507_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_dec_ref_known(v___x_2508_, 1);
v___y_2471_ = v___y_2490_;
v___y_2472_ = v___y_2491_;
v___y_2473_ = v___y_2492_;
v___y_2474_ = v___y_2493_;
v___y_2475_ = v___y_2495_;
v___y_2476_ = v___y_2494_;
v___y_2477_ = v___y_2496_;
v___y_2478_ = v___y_2497_;
goto v___jp_2470_;
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec_ref(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___x_2429_);
lean_dec(v_mainModuleName_2340_);
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2487_);
lean_dec(v_oleanFileName_x3f_2342_);
v___y_2471_ = v___y_2490_;
v___y_2472_ = v___y_2491_;
v___y_2473_ = v___y_2492_;
v___y_2474_ = v___y_2493_;
v___y_2475_ = v___y_2495_;
v___y_2476_ = v___y_2494_;
v___y_2477_ = v___y_2496_;
v___y_2478_ = v___y_2497_;
goto v___jp_2470_;
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec_ref(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2493_);
lean_dec_ref(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec_ref(v___y_2487_);
lean_dec_ref(v___x_2429_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
}
v___jp_2519_:
{
if (v_printStats_2347_ == 0)
{
v___y_2487_ = v___y_2520_;
v___y_2488_ = v___y_2521_;
v___y_2489_ = v___y_2522_;
v___y_2490_ = v___y_2523_;
v___y_2491_ = v___y_2524_;
v___y_2492_ = v___y_2525_;
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2528_;
v___y_2495_ = v___y_2527_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
goto v___jp_2486_;
}
else
{
lean_object* v___x_2531_; 
lean_inc_ref(v___y_2529_);
v___x_2531_ = l_Lean_Environment_displayStats(v___y_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_dec_ref_known(v___x_2531_, 1);
v___y_2487_ = v___y_2520_;
v___y_2488_ = v___y_2521_;
v___y_2489_ = v___y_2522_;
v___y_2490_ = v___y_2523_;
v___y_2491_ = v___y_2524_;
v___y_2492_ = v___y_2525_;
v___y_2493_ = v___y_2526_;
v___y_2494_ = v___y_2528_;
v___y_2495_ = v___y_2527_;
v___y_2496_ = v___y_2529_;
v___y_2497_ = v___y_2530_;
goto v___jp_2486_;
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec_ref(v___y_2520_);
lean_dec_ref(v___x_2429_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
}
v___jp_2540_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2351_) == 1)
{
lean_object* v_val_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_val_2552_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2351_, 0);
lean_inc(v_val_2552_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2351_, 1);
lean_inc_ref(v___y_2548_);
v___x_2553_ = l_Lean_Language_Lean_truncateToHeader(v___y_2548_);
v___x_2554_ = lean_apply_3(v___y_2543_, v_val_2552_, v___x_2553_, lean_box(0));
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_dec_ref_known(v___x_2554_, 1);
lean_inc_ref(v___y_2544_);
v___y_2520_ = v___y_2541_;
v___y_2521_ = v___y_2542_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___y_2550_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2544_;
v___y_2530_ = v___y_2551_;
goto v___jp_2519_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2548_);
lean_dec_ref(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec_ref(v___y_2541_);
lean_dec_ref(v___x_2429_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2554_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2554_);
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
else
{
lean_dec_ref(v___y_2543_);
lean_dec(v_incrHeaderSaveFileName_x3f_2351_);
lean_inc_ref(v___y_2544_);
v___y_2520_ = v___y_2541_;
v___y_2521_ = v___y_2542_;
v___y_2522_ = v___y_2544_;
v___y_2523_ = v___y_2545_;
v___y_2524_ = v___y_2546_;
v___y_2525_ = v___y_2547_;
v___y_2526_ = v___y_2548_;
v___y_2527_ = v___y_2550_;
v___y_2528_ = v___y_2549_;
v___y_2529_ = v___y_2544_;
v___y_2530_ = v___y_2551_;
goto v___jp_2519_;
}
}
v___jp_2563_:
{
size_t v_sz_2573_; size_t v___x_2574_; lean_object* v___x_2575_; 
v_sz_2573_ = lean_array_size(v___y_2572_);
v___x_2574_ = ((size_t)0ULL);
v___x_2575_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v___y_2572_, v_sz_2573_, v___x_2574_, v___y_2568_);
lean_dec_ref(v___y_2572_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; lean_object* v___f_2578_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_n(v_a_2576_, 2);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = lean_box(v___x_2366_);
v___f_2578_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 5, 2);
lean_closure_set(v___f_2578_, 0, v_a_2576_);
lean_closure_set(v___f_2578_, 1, v___x_2577_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2349_) == 1)
{
lean_object* v_val_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_val_2579_ = lean_ctor_get(v_incrSaveFileName_x3f_2349_, 0);
lean_inc(v_val_2579_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2349_, 1);
v___x_2580_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2566_);
lean_inc_ref(v___y_2569_);
v___x_2581_ = l_Lean_Elab_runFrontend___lam__2(v_a_2576_, v___x_2366_, v_val_2579_, v___y_2569_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_dec_ref_known(v___x_2581_, 1);
lean_inc_ref(v___y_2564_);
v___y_2541_ = v___y_2564_;
v___y_2542_ = v___y_2565_;
v___y_2543_ = v___f_2578_;
v___y_2544_ = v_a_2576_;
v___y_2545_ = v___y_2566_;
v___y_2546_ = v___y_2564_;
v___y_2547_ = v___y_2567_;
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___x_2574_;
v___y_2550_ = v___y_2570_;
v___y_2551_ = v___y_2571_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec_ref(v___f_2578_);
lean_dec(v_a_2576_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___y_2566_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___x_2429_);
lean_dec(v_incrHeaderSaveFileName_x3f_2351_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_dec(v_incrSaveFileName_x3f_2349_);
lean_inc_ref(v___y_2564_);
v___y_2541_ = v___y_2564_;
v___y_2542_ = v___y_2565_;
v___y_2543_ = v___f_2578_;
v___y_2544_ = v_a_2576_;
v___y_2545_ = v___y_2566_;
v___y_2546_ = v___y_2564_;
v___y_2547_ = v___y_2567_;
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___x_2574_;
v___y_2550_ = v___y_2570_;
v___y_2551_ = v___y_2571_;
goto v___jp_2540_;
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v___y_2566_);
lean_dec_ref(v___y_2564_);
lean_dec_ref(v___x_2429_);
lean_dec(v_incrHeaderSaveFileName_x3f_2351_);
lean_dec(v_incrSaveFileName_x3f_2349_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v_a_2590_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2575_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2575_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
v___jp_2598_:
{
lean_object* v___x_2604_; 
lean_inc_ref(v___y_2599_);
v___x_2604_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2599_, v___y_2602_, v_jsonOutput_2344_, v___y_2603_);
lean_dec(v___y_2603_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2626_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2626_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2626_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; 
lean_inc_ref(v___y_2600_);
v___x_2609_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2600_);
if (lean_obj_tag(v___x_2609_) == 1)
{
lean_object* v_val_2610_; lean_object* v_env_2611_; lean_object* v_scopes_2612_; lean_object* v___x_2613_; lean_object* v_opts_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_del_object(v___x_2607_);
v_val_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v_env_2611_ = lean_ctor_get(v_val_2610_, 0);
lean_inc_ref(v_env_2611_);
v_scopes_2612_ = lean_ctor_get(v_val_2610_, 2);
lean_inc(v_scopes_2612_);
lean_dec(v_val_2610_);
lean_inc(v___y_2601_);
v___x_2613_ = l_List_get_x21Internal___redArg(v___x_2361_, v_scopes_2612_, v___y_2601_);
lean_dec(v_scopes_2612_);
v_opts_2614_ = lean_ctor_get(v___x_2613_, 1);
lean_inc_ref(v_opts_2614_);
lean_dec(v___x_2613_);
v___x_2615_ = lean_mk_empty_array_with_capacity(v___y_2601_);
lean_inc_ref(v___x_2615_);
lean_inc_ref(v___y_2600_);
v___x_2616_ = l_Lean_Language_Lean_foldCmdSnaps_x3f___redArg(v___y_2600_, v___x_2615_, v___f_2359_);
if (lean_obj_tag(v___x_2616_) == 0)
{
uint8_t v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = lean_unbox(v_a_2605_);
v___x_2618_ = lean_unbox(v_a_2605_);
lean_dec(v_a_2605_);
v___y_2564_ = v_opts_2614_;
v___y_2565_ = v___x_2617_;
v___y_2566_ = v___y_2599_;
v___y_2567_ = v___x_2618_;
v___y_2568_ = v_env_2611_;
v___y_2569_ = v___y_2600_;
v___y_2570_ = v___y_2601_;
v___y_2571_ = v___y_2602_;
v___y_2572_ = v___x_2615_;
goto v___jp_2563_;
}
else
{
lean_object* v_val_2619_; uint8_t v___x_2620_; uint8_t v___x_2621_; 
lean_dec_ref(v___x_2615_);
v_val_2619_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_val_2619_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2620_ = lean_unbox(v_a_2605_);
v___x_2621_ = lean_unbox(v_a_2605_);
lean_dec(v_a_2605_);
v___y_2564_ = v_opts_2614_;
v___y_2565_ = v___x_2620_;
v___y_2566_ = v___y_2599_;
v___y_2567_ = v___x_2621_;
v___y_2568_ = v_env_2611_;
v___y_2569_ = v___y_2600_;
v___y_2570_ = v___y_2601_;
v___y_2571_ = v___y_2602_;
v___y_2572_ = v_val_2619_;
goto v___jp_2563_;
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2624_; 
lean_dec(v___x_2609_);
lean_dec(v_a_2605_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2429_);
lean_dec(v_incrHeaderSaveFileName_x3f_2351_);
lean_dec(v_incrSaveFileName_x3f_2349_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v___x_2622_ = lean_box(0);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2622_);
v___x_2624_ = v___x_2607_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v___x_2429_);
lean_dec(v_incrHeaderSaveFileName_x3f_2351_);
lean_dec(v_incrSaveFileName_x3f_2349_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v_a_2627_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2604_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2604_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
v___jp_2635_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2639_ = l_Lean_Language_Lean_process(v___y_2636_, v_a_2638_, v___x_2429_);
lean_inc_ref(v___x_2639_);
v___x_2640_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2639_);
v___x_2641_ = lean_box(1);
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_array_get_size(v_errorOnKinds_2345_);
v___x_2644_ = lean_nat_dec_lt(v___x_2642_, v___x_2643_);
if (v___x_2644_ == 0)
{
v___y_2599_ = v___x_2640_;
v___y_2600_ = v___x_2639_;
v___y_2601_ = v___x_2642_;
v___y_2602_ = v___y_2637_;
v___y_2603_ = v___x_2641_;
goto v___jp_2598_;
}
else
{
uint8_t v___x_2645_; 
v___x_2645_ = lean_nat_dec_le(v___x_2643_, v___x_2643_);
if (v___x_2645_ == 0)
{
if (v___x_2644_ == 0)
{
v___y_2599_ = v___x_2640_;
v___y_2600_ = v___x_2639_;
v___y_2601_ = v___x_2642_;
v___y_2602_ = v___y_2637_;
v___y_2603_ = v___x_2641_;
goto v___jp_2598_;
}
else
{
size_t v___x_2646_; size_t v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = ((size_t)0ULL);
v___x_2647_ = lean_usize_of_nat(v___x_2643_);
v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2345_, v___x_2646_, v___x_2647_, v___x_2641_);
v___y_2599_ = v___x_2640_;
v___y_2600_ = v___x_2639_;
v___y_2601_ = v___x_2642_;
v___y_2602_ = v___y_2637_;
v___y_2603_ = v___x_2648_;
goto v___jp_2598_;
}
}
else
{
size_t v___x_2649_; size_t v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = ((size_t)0ULL);
v___x_2650_ = lean_usize_of_nat(v___x_2643_);
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2345_, v___x_2649_, v___x_2650_, v___x_2641_);
v___y_2599_ = v___x_2640_;
v___y_2600_ = v___x_2639_;
v___y_2601_ = v___x_2642_;
v___y_2602_ = v___y_2637_;
v___y_2603_ = v___x_2651_;
goto v___jp_2598_;
}
}
}
v___jp_2652_:
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_a_2655_);
v___y_2636_ = v___y_2653_;
v___y_2637_ = v___y_2654_;
v_a_2638_ = v___x_2656_;
goto v___jp_2635_;
}
v___jp_2658_:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___f_2665_; 
v___x_2660_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2338_, v___x_2657_, v___y_2659_);
v___x_2661_ = l_Lean_Elab_async;
v___x_2662_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2660_, v___x_2661_, v___x_2366_);
v___x_2663_ = lean_box_uint32(v_trustLevel_2341_);
v___x_2664_ = lean_box(v___x_2366_);
lean_inc(v_mainModuleName_2340_);
lean_inc_ref(v___x_2662_);
v___f_2665_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 10, 7);
lean_closure_set(v___f_2665_, 0, v_setup_x3f_2348_);
lean_closure_set(v___f_2665_, 1, v___f_2360_);
lean_closure_set(v___f_2665_, 2, v___x_2662_);
lean_closure_set(v___f_2665_, 3, v_plugins_2346_);
lean_closure_set(v___f_2665_, 4, v___x_2663_);
lean_closure_set(v___f_2665_, 5, v___x_2664_);
lean_closure_set(v___f_2665_, 6, v_mainModuleName_2340_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2350_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_box(0);
v___y_2636_ = v___f_2665_;
v___y_2637_ = v___x_2662_;
v_a_2638_ = v___x_2666_;
goto v___jp_2635_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
v_val_2667_ = lean_ctor_get(v_incrLoadFileName_x3f_2350_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2350_, 1);
v___x_2668_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2667_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v_snap_2670_; lean_object* v_initModIdxs_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v_snap_2670_ = lean_ctor_get(v_a_2669_, 0);
lean_inc_ref(v_snap_2670_);
v_initModIdxs_2671_ = lean_ctor_get(v_a_2669_, 1);
lean_inc_ref(v_initModIdxs_2671_);
lean_dec(v_a_2669_);
lean_inc(v_mainModuleName_2340_);
v___x_2672_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2670_, v_mainModuleName_2340_);
lean_inc_ref(v___x_2672_);
v___x_2673_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2672_);
v___x_2674_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2673_);
if (lean_obj_tag(v___x_2674_) == 1)
{
lean_object* v_val_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; 
v_val_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v___x_2674_, 1);
lean_inc_ref(v___x_2662_);
v___f_2676_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__5___boxed), 4, 3);
lean_closure_set(v___f_2676_, 0, v_val_2675_);
lean_closure_set(v___f_2676_, 1, v_initModIdxs_2671_);
lean_closure_set(v___f_2676_, 2, v___x_2662_);
v___x_2677_ = l_Lean_withImporting___redArg(v___f_2676_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref_known(v___x_2677_, 1);
v___x_2678_ = lean_enable_initializer_execution();
v___y_2653_ = v___f_2665_;
v___y_2654_ = v___x_2662_;
v_a_2655_ = v___x_2672_;
goto v___jp_2652_;
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec_ref(v___x_2672_);
lean_dec_ref(v___f_2665_);
lean_dec_ref(v___x_2662_);
lean_dec_ref(v___x_2429_);
lean_dec(v_incrHeaderSaveFileName_x3f_2351_);
lean_dec(v_incrSaveFileName_x3f_2349_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v_a_2679_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2677_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2677_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_dec(v___x_2674_);
lean_dec_ref(v_initModIdxs_2671_);
v___y_2653_ = v___f_2665_;
v___y_2654_ = v___x_2662_;
v_a_2655_ = v___x_2672_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v___f_2665_);
lean_dec_ref(v___x_2662_);
lean_dec_ref(v___x_2429_);
lean_dec(v_incrHeaderSaveFileName_x3f_2351_);
lean_dec(v_incrSaveFileName_x3f_2349_);
lean_dec(v_oleanFileName_x3f_2342_);
lean_dec(v_mainModuleName_2340_);
v_a_2687_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2668_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2668_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2696_, lean_object* v_opts_2697_, lean_object* v_fileName_2698_, lean_object* v_mainModuleName_2699_, lean_object* v_trustLevel_2700_, lean_object* v_oleanFileName_x3f_2701_, lean_object* v_ileanFileName_x3f_2702_, lean_object* v_jsonOutput_2703_, lean_object* v_errorOnKinds_2704_, lean_object* v_plugins_2705_, lean_object* v_printStats_2706_, lean_object* v_setup_x3f_2707_, lean_object* v_incrSaveFileName_x3f_2708_, lean_object* v_incrLoadFileName_x3f_2709_, lean_object* v_incrHeaderSaveFileName_x3f_2710_, lean_object* v_a_2711_){
_start:
{
uint32_t v_trustLevel_boxed_2712_; uint8_t v_jsonOutput_boxed_2713_; uint8_t v_printStats_boxed_2714_; lean_object* v_res_2715_; 
v_trustLevel_boxed_2712_ = lean_unbox_uint32(v_trustLevel_2700_);
lean_dec(v_trustLevel_2700_);
v_jsonOutput_boxed_2713_ = lean_unbox(v_jsonOutput_2703_);
v_printStats_boxed_2714_ = lean_unbox(v_printStats_2706_);
v_res_2715_ = l_Lean_Elab_runFrontend(v_input_2696_, v_opts_2697_, v_fileName_2698_, v_mainModuleName_2699_, v_trustLevel_boxed_2712_, v_oleanFileName_x3f_2701_, v_ileanFileName_x3f_2702_, v_jsonOutput_boxed_2713_, v_errorOnKinds_2704_, v_plugins_2705_, v_printStats_boxed_2714_, v_setup_x3f_2707_, v_incrSaveFileName_x3f_2708_, v_incrLoadFileName_x3f_2709_, v_incrHeaderSaveFileName_x3f_2710_);
lean_dec_ref(v_errorOnKinds_2704_);
lean_dec(v_ileanFileName_x3f_2702_);
return v_res_2715_;
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
