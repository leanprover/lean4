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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Command_elabCommandTopLevel(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleArtifacts_toJson(lean_object*);
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
extern lean_object* l_Lean_Linter_codeQualityLogExt;
lean_object* l_Lean_PersistentEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_276_; lean_object* v_commandState_277_; lean_object* v_parserState_278_; lean_object* v_cmdPos_279_; lean_object* v_commands_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_310_; 
v___x_276_ = lean_st_ref_take(v_a_274_);
v_commandState_277_ = lean_ctor_get(v___x_276_, 0);
v_parserState_278_ = lean_ctor_get(v___x_276_, 1);
v_cmdPos_279_ = lean_ctor_get(v___x_276_, 2);
v_commands_280_ = lean_ctor_get(v___x_276_, 3);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_310_ == 0)
{
v___x_282_ = v___x_276_;
v_isShared_283_ = v_isSharedCheck_310_;
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
v_isShared_283_ = v_isSharedCheck_310_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_env_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v_prevLinterStates_294_; lean_object* v_codeQualityEntryTasks_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_308_; 
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
v_codeQualityEntryTasks_295_ = lean_ctor_get(v_commandState_277_, 12);
v_isSharedCheck_308_ = !lean_is_exclusive(v_commandState_277_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v_commandState_277_, 1);
lean_dec(v_unused_309_);
v___x_297_ = v_commandState_277_;
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_codeQualityEntryTasks_295_);
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
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_308_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v_msgs_273_);
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_env_284_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_msgs_273_);
lean_ctor_set(v_reuseFailAlloc_307_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_307_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_307_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_307_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_307_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_307_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_307_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_307_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_307_, 10, v_snapshotTasks_293_);
lean_ctor_set(v_reuseFailAlloc_307_, 11, v_prevLinterStates_294_);
lean_ctor_set(v_reuseFailAlloc_307_, 12, v_codeQualityEntryTasks_295_);
v___x_300_ = v_reuseFailAlloc_307_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_302_; 
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_300_);
v___x_302_ = v___x_282_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_parserState_278_);
lean_ctor_set(v_reuseFailAlloc_306_, 2, v_cmdPos_279_);
lean_ctor_set(v_reuseFailAlloc_306_, 3, v_commands_280_);
v___x_302_ = v_reuseFailAlloc_306_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_st_ref_put(v_a_274_, v___x_302_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___redArg___boxed(lean_object* v_msgs_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_311_, v_a_312_);
lean_dec(v_a_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages(lean_object* v_msgs_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Elab_Frontend_setMessages___redArg(v_msgs_315_, v_a_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_setMessages___boxed(lean_object* v_msgs_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Elab_Frontend_setMessages(v_msgs_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg(lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
lean_inc_ref(v_a_325_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v_a_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___redArg___boxed(lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Elab_Frontend_getInputContext___redArg(v_a_328_);
lean_dec_ref(v_a_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext(lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
lean_inc_ref(v_a_331_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v_a_331_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_getInputContext___boxed(lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Elab_Frontend_getInputContext(v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0(lean_object* v_a_339_, lean_object* v___x_340_, lean_object* v_a_341_, lean_object* v_messages_342_, lean_object* v_x_343_){
_start:
{
lean_object* v___x_344_; 
lean_inc_ref(v_a_339_);
v___x_344_ = l_Lean_Parser_parseCommand(v_a_339_, v___x_340_, v_a_341_, v_messages_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___lam__0___boxed(lean_object* v_a_345_, lean_object* v___x_346_, lean_object* v_a_347_, lean_object* v_messages_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Elab_Frontend_processCommand___lam__0(v_a_345_, v___x_346_, v_a_347_, v_messages_348_, v_x_349_);
lean_dec_ref(v_a_345_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand(lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v_a_359_; lean_object* v_env_360_; lean_object* v_messages_361_; lean_object* v_scopes_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v_opts_365_; lean_object* v_currNamespace_366_; lean_object* v_openDecls_367_; lean_object* v___x_368_; lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_snd_373_; lean_object* v_fst_374_; lean_object* v_fst_375_; lean_object* v_snd_376_; lean_object* v___x_377_; lean_object* v_commandState_378_; lean_object* v_parserState_379_; lean_object* v_cmdPos_380_; lean_object* v_commands_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_411_; 
v___x_355_ = l_Lean_Elab_Frontend_updateCmdPos___redArg(v_a_353_);
lean_dec_ref(v___x_355_);
v___x_356_ = l_Lean_Elab_Frontend_getCommandState___redArg(v_a_353_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref(v___x_356_);
v___x_358_ = l_Lean_Elab_Frontend_getParserState___redArg(v_a_353_);
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref(v___x_358_);
v_env_360_ = lean_ctor_get(v_a_357_, 0);
lean_inc_ref(v_env_360_);
v_messages_361_ = lean_ctor_get(v_a_357_, 1);
lean_inc_ref(v_messages_361_);
v_scopes_362_ = lean_ctor_get(v_a_357_, 2);
lean_inc(v_scopes_362_);
lean_dec(v_a_357_);
v___x_363_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_364_ = l_List_head_x21___redArg(v___x_363_, v_scopes_362_);
lean_dec(v_scopes_362_);
v_opts_365_ = lean_ctor_get(v___x_364_, 1);
lean_inc_ref_n(v_opts_365_, 2);
v_currNamespace_366_ = lean_ctor_get(v___x_364_, 2);
lean_inc(v_currNamespace_366_);
v_openDecls_367_ = lean_ctor_get(v___x_364_, 3);
lean_inc(v_openDecls_367_);
lean_dec(v___x_364_);
v___x_368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_368_, 0, v_env_360_);
lean_ctor_set(v___x_368_, 1, v_opts_365_);
lean_ctor_set(v___x_368_, 2, v_currNamespace_366_);
lean_ctor_set(v___x_368_, 3, v_openDecls_367_);
lean_inc_ref(v_a_352_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Elab_Frontend_processCommand___lam__0___boxed), 5, 4);
lean_closure_set(v___f_369_, 0, v_a_352_);
lean_closure_set(v___f_369_, 1, v___x_368_);
lean_closure_set(v___f_369_, 2, v_a_359_);
lean_closure_set(v___f_369_, 3, v_messages_361_);
v___x_370_ = ((lean_object*)(l_Lean_Elab_Frontend_processCommand___closed__0));
v___x_371_ = lean_box(0);
v___x_372_ = lean_profileit(v___x_370_, v_opts_365_, v___f_369_, v___x_371_);
lean_dec_ref(v_opts_365_);
v_snd_373_ = lean_ctor_get(v___x_372_, 1);
lean_inc(v_snd_373_);
v_fst_374_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_fst_374_);
lean_dec(v___x_372_);
v_fst_375_ = lean_ctor_get(v_snd_373_, 0);
lean_inc(v_fst_375_);
v_snd_376_ = lean_ctor_get(v_snd_373_, 1);
lean_inc(v_snd_376_);
lean_dec(v_snd_373_);
v___x_377_ = lean_st_ref_take(v_a_353_);
v_commandState_378_ = lean_ctor_get(v___x_377_, 0);
v_parserState_379_ = lean_ctor_get(v___x_377_, 1);
v_cmdPos_380_ = lean_ctor_get(v___x_377_, 2);
v_commands_381_ = lean_ctor_get(v___x_377_, 3);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_411_ == 0)
{
v___x_383_ = v___x_377_;
v_isShared_384_ = v_isSharedCheck_411_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_commands_381_);
lean_inc(v_cmdPos_380_);
lean_inc(v_parserState_379_);
lean_inc(v_commandState_378_);
lean_dec(v___x_377_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_411_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
lean_inc(v_fst_374_);
v___x_385_ = lean_array_push(v_commands_381_, v_fst_374_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 3, v___x_385_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_commandState_378_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_parserState_379_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_cmdPos_380_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v___x_385_);
v___x_387_ = v_reuseFailAlloc_410_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = lean_st_ref_put(v_a_353_, v___x_387_);
v___x_389_ = l_Lean_Elab_Frontend_setParserState___redArg(v_fst_375_, v_a_353_);
lean_dec_ref(v___x_389_);
v___x_390_ = l_Lean_Elab_Frontend_setMessages___redArg(v_snd_376_, v_a_353_);
lean_dec_ref(v___x_390_);
lean_inc(v_fst_374_);
v___x_391_ = l_Lean_Elab_Frontend_elabCommandAtFrontend(v_fst_374_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_400_; 
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_401_);
v___x_393_ = v___x_391_;
v_isShared_394_ = v_isSharedCheck_400_;
goto v_resetjp_392_;
}
else
{
lean_dec(v___x_391_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_400_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = l_Lean_Parser_isTerminalCommand(v_fst_374_);
v___x_396_ = lean_box(v___x_395_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
lean_dec(v_fst_374_);
v_a_402_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_391_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_391_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommand___boxed(lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_Frontend_processCommand(v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands(lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Elab_Frontend_processCommand(v_a_416_, v_a_417_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_430_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_430_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint8_t v___x_424_; 
v___x_424_ = lean_unbox(v_a_420_);
lean_dec(v_a_420_);
if (v___x_424_ == 0)
{
lean_del_object(v___x_422_);
goto _start;
}
else
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_box(0);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_426_);
v___x_428_ = v___x_422_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_431_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_419_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_419_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Frontend_processCommands___boxed(lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Elab_Frontend_processCommands(v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(lean_object* v_a_443_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_445_ = l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(v_a_443_, v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(lean_object* v_as_446_, size_t v_i_447_, size_t v_stop_448_, lean_object* v_b_449_){
_start:
{
lean_object* v___y_451_; uint8_t v___x_455_; 
v___x_455_ = lean_usize_dec_eq(v_i_447_, v_stop_448_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
v___x_456_ = lean_array_uget_borrowed(v_as_446_, v_i_447_);
if (lean_obj_tag(v___x_456_) == 0)
{
v___y_451_ = v_b_449_;
goto v___jp_450_;
}
else
{
lean_object* v_val_457_; lean_object* v___x_458_; 
v_val_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_val_457_);
v___x_458_ = lean_array_push(v_b_449_, v_val_457_);
v___y_451_ = v___x_458_;
goto v___jp_450_;
}
}
else
{
return v_b_449_;
}
v___jp_450_:
{
size_t v___x_452_; size_t v___x_453_; 
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_i_447_, v___x_452_);
v_i_447_ = v___x_453_;
v_b_449_ = v___y_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1___boxed(lean_object* v_as_459_, lean_object* v_i_460_, lean_object* v_stop_461_, lean_object* v_b_462_){
_start:
{
size_t v_i_boxed_463_; size_t v_stop_boxed_464_; lean_object* v_res_465_; 
v_i_boxed_463_ = lean_unbox_usize(v_i_460_);
lean_dec(v_i_460_);
v_stop_boxed_464_ = lean_unbox_usize(v_stop_461_);
lean_dec(v_stop_461_);
v_res_465_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_459_, v_i_boxed_463_, v_stop_boxed_464_, v_b_462_);
lean_dec_ref(v_as_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(lean_object* v_as_468_, lean_object* v_start_469_, lean_object* v_stop_470_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_472_ = lean_nat_dec_lt(v_start_469_, v_stop_470_);
if (v___x_472_ == 0)
{
return v___x_471_;
}
else
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_array_get_size(v_as_468_);
v___x_474_ = lean_nat_dec_le(v_stop_470_, v___x_473_);
if (v___x_474_ == 0)
{
uint8_t v___x_475_; 
v___x_475_ = lean_nat_dec_lt(v_start_469_, v___x_473_);
if (v___x_475_ == 0)
{
return v___x_471_;
}
else
{
size_t v___x_476_; size_t v___x_477_; lean_object* v___x_478_; 
v___x_476_ = lean_usize_of_nat(v_start_469_);
v___x_477_ = lean_usize_of_nat(v___x_473_);
v___x_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_468_, v___x_476_, v___x_477_, v___x_471_);
return v___x_478_;
}
}
else
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_usize_of_nat(v_start_469_);
v___x_480_ = lean_usize_of_nat(v_stop_470_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1_spec__1(v_as_468_, v___x_479_, v___x_480_, v___x_471_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___boxed(lean_object* v_as_482_, lean_object* v_start_483_, lean_object* v_stop_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v_as_482_, v_start_483_, v_stop_484_);
lean_dec(v_stop_484_);
lean_dec(v_start_483_);
lean_dec_ref(v_as_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(size_t v_sz_486_, size_t v_i_487_, lean_object* v_bs_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_489_ == 0)
{
return v_bs_488_;
}
else
{
lean_object* v_v_490_; lean_object* v_diagnostics_491_; lean_object* v_msgLog_492_; lean_object* v___x_493_; lean_object* v_bs_x27_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_v_490_ = lean_array_uget_borrowed(v_bs_488_, v_i_487_);
v_diagnostics_491_ = lean_ctor_get(v_v_490_, 1);
v_msgLog_492_ = lean_ctor_get(v_diagnostics_491_, 0);
lean_inc_ref(v_msgLog_492_);
v___x_493_ = lean_unsigned_to_nat(0u);
v_bs_x27_494_ = lean_array_uset(v_bs_488_, v_i_487_, v___x_493_);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_add(v_i_487_, v___x_495_);
v___x_497_ = lean_array_uset(v_bs_x27_494_, v_i_487_, v_msgLog_492_);
v_i_487_ = v___x_496_;
v_bs_488_ = v___x_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4___boxed(lean_object* v_sz_499_, lean_object* v_i_500_, lean_object* v_bs_501_){
_start:
{
size_t v_sz_boxed_502_; size_t v_i_boxed_503_; lean_object* v_res_504_; 
v_sz_boxed_502_ = lean_unbox_usize(v_sz_499_);
lean_dec(v_sz_499_);
v_i_boxed_503_ = lean_unbox_usize(v_i_500_);
lean_dec(v_i_500_);
v_res_504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_boxed_502_, v_i_boxed_503_, v_bs_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(size_t v_sz_505_, size_t v_i_506_, lean_object* v_bs_507_){
_start:
{
uint8_t v___x_508_; 
v___x_508_ = lean_usize_dec_lt(v_i_506_, v_sz_505_);
if (v___x_508_ == 0)
{
return v_bs_507_;
}
else
{
lean_object* v_v_509_; lean_object* v_elabSnap_510_; lean_object* v_infoTreeSnap_511_; lean_object* v___x_512_; lean_object* v_infoTree_x3f_513_; lean_object* v___x_514_; lean_object* v_bs_x27_515_; size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; 
v_v_509_ = lean_array_uget_borrowed(v_bs_507_, v_i_506_);
v_elabSnap_510_ = lean_ctor_get(v_v_509_, 3);
v_infoTreeSnap_511_ = lean_ctor_get(v_elabSnap_510_, 3);
lean_inc_ref(v_infoTreeSnap_511_);
v___x_512_ = l_Lean_Language_SnapshotTask_get___redArg(v_infoTreeSnap_511_);
v_infoTree_x3f_513_ = lean_ctor_get(v___x_512_, 2);
lean_inc(v_infoTree_x3f_513_);
lean_dec(v___x_512_);
v___x_514_ = lean_unsigned_to_nat(0u);
v_bs_x27_515_ = lean_array_uset(v_bs_507_, v_i_506_, v___x_514_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_506_, v___x_516_);
v___x_518_ = lean_array_uset(v_bs_x27_515_, v_i_506_, v_infoTree_x3f_513_);
v_i_506_ = v___x_517_;
v_bs_507_ = v___x_518_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0___boxed(lean_object* v_sz_520_, lean_object* v_i_521_, lean_object* v_bs_522_){
_start:
{
size_t v_sz_boxed_523_; size_t v_i_boxed_524_; lean_object* v_res_525_; 
v_sz_boxed_523_ = lean_unbox_usize(v_sz_520_);
lean_dec(v_sz_520_);
v_i_boxed_524_ = lean_unbox_usize(v_i_521_);
lean_dec(v_i_521_);
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_boxed_523_, v_i_boxed_524_, v_bs_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(size_t v_sz_526_, size_t v_i_527_, lean_object* v_bs_528_){
_start:
{
uint8_t v___x_529_; 
v___x_529_ = lean_usize_dec_lt(v_i_527_, v_sz_526_);
if (v___x_529_ == 0)
{
return v_bs_528_;
}
else
{
lean_object* v_v_530_; lean_object* v_stx_531_; lean_object* v___x_532_; lean_object* v_bs_x27_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v_v_530_ = lean_array_uget_borrowed(v_bs_528_, v_i_527_);
v_stx_531_ = lean_ctor_get(v_v_530_, 1);
lean_inc(v_stx_531_);
v___x_532_ = lean_unsigned_to_nat(0u);
v_bs_x27_533_ = lean_array_uset(v_bs_528_, v_i_527_, v___x_532_);
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_add(v_i_527_, v___x_534_);
v___x_536_ = lean_array_uset(v_bs_x27_533_, v_i_527_, v_stx_531_);
v_i_527_ = v___x_535_;
v_bs_528_ = v___x_536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2___boxed(lean_object* v_sz_538_, lean_object* v_i_539_, lean_object* v_bs_540_){
_start:
{
size_t v_sz_boxed_541_; size_t v_i_boxed_542_; lean_object* v_res_543_; 
v_sz_boxed_541_ = lean_unbox_usize(v_sz_538_);
lean_dec(v_sz_538_);
v_i_boxed_542_ = lean_unbox_usize(v_i_539_);
lean_dec(v_i_539_);
v_res_543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_boxed_541_, v_i_boxed_542_, v_bs_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(lean_object* v_as_544_, size_t v_i_545_, size_t v_stop_546_, lean_object* v_b_547_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = lean_usize_dec_eq(v_i_545_, v_stop_546_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; size_t v___x_551_; size_t v___x_552_; 
v___x_549_ = lean_array_uget_borrowed(v_as_544_, v_i_545_);
lean_inc(v___x_549_);
v___x_550_ = l_Lean_MessageLog_append(v_b_547_, v___x_549_);
v___x_551_ = ((size_t)1ULL);
v___x_552_ = lean_usize_add(v_i_545_, v___x_551_);
v_i_545_ = v___x_552_;
v_b_547_ = v___x_550_;
goto _start;
}
else
{
return v_b_547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5___boxed(lean_object* v_as_554_, lean_object* v_i_555_, lean_object* v_stop_556_, lean_object* v_b_557_){
_start:
{
size_t v_i_boxed_558_; size_t v_stop_boxed_559_; lean_object* v_res_560_; 
v_i_boxed_558_ = lean_unbox_usize(v_i_555_);
lean_dec(v_i_555_);
v_stop_boxed_559_ = lean_unbox_usize(v_stop_556_);
lean_dec(v_stop_556_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v_as_554_, v_i_boxed_558_, v_stop_boxed_559_, v_b_557_);
lean_dec_ref(v_as_554_);
return v_res_560_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_unsigned_to_nat(32u);
v___x_562_ = lean_mk_empty_array_with_capacity(v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1(void){
_start:
{
size_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_564_ = ((size_t)5ULL);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_unsigned_to_nat(32u);
v___x_567_ = lean_mk_empty_array_with_capacity(v___x_566_);
v___x_568_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__0);
v___x_569_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_565_);
lean_ctor_set(v___x_569_, 3, v___x_565_);
lean_ctor_set_usize(v___x_569_, 4, v___x_564_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = l_Lean_NameSet_empty;
v___x_571_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__1);
v___x_572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
lean_ctor_set(v___x_572_, 2, v___x_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(lean_object* v_inputCtx_573_, lean_object* v_initialSnap_574_, lean_object* v_t_575_, lean_object* v_commands_576_){
_start:
{
lean_object* v_snap_578_; lean_object* v_parserState_579_; lean_object* v_elabSnap_580_; lean_object* v_nextCmdSnap_x3f_581_; lean_object* v_commands_582_; 
v_snap_578_ = lean_task_get_own(v_t_575_);
v_parserState_579_ = lean_ctor_get(v_snap_578_, 2);
lean_inc_ref(v_parserState_579_);
v_elabSnap_580_ = lean_ctor_get(v_snap_578_, 3);
lean_inc_ref(v_elabSnap_580_);
v_nextCmdSnap_x3f_581_ = lean_ctor_get(v_snap_578_, 4);
lean_inc(v_nextCmdSnap_x3f_581_);
v_commands_582_ = lean_array_push(v_commands_576_, v_snap_578_);
if (lean_obj_tag(v_nextCmdSnap_x3f_581_) == 1)
{
lean_object* v_val_583_; lean_object* v_task_584_; 
lean_dec_ref(v_elabSnap_580_);
lean_dec_ref(v_parserState_579_);
v_val_583_ = lean_ctor_get(v_nextCmdSnap_x3f_581_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v_nextCmdSnap_x3f_581_, 1);
v_task_584_ = lean_ctor_get(v_val_583_, 3);
lean_inc_ref(v_task_584_);
lean_dec(v_val_583_);
v_t_575_ = v_task_584_;
v_commands_576_ = v_commands_582_;
goto _start;
}
else
{
lean_object* v___x_586_; lean_object* v___y_588_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; size_t v_sz_636_; size_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
lean_dec(v_nextCmdSnap_x3f_581_);
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
lean_inc_ref(v_initialSnap_574_);
v___x_634_ = l_Lean_Language_toSnapshotTree___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__3(v_initialSnap_574_);
v___x_635_ = l_Lean_Language_SnapshotTree_getAll(v___x_634_);
v_sz_636_ = lean_array_size(v___x_635_);
v___x_637_ = ((size_t)0ULL);
v___x_638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__4(v_sz_636_, v___x_637_, v___x_635_);
v___x_639_ = lean_array_get_size(v___x_638_);
v___x_640_ = lean_nat_dec_lt(v___x_586_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec_ref(v___x_638_);
v___y_588_ = v___x_633_;
goto v___jp_587_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = lean_nat_dec_le(v___x_639_, v___x_639_);
if (v___x_641_ == 0)
{
if (v___x_640_ == 0)
{
lean_dec_ref(v___x_638_);
v___y_588_ = v___x_633_;
goto v___jp_587_;
}
else
{
size_t v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_usize_of_nat(v___x_639_);
v___x_643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_638_, v___x_637_, v___x_642_, v___x_633_);
lean_dec_ref(v___x_638_);
v___y_588_ = v___x_643_;
goto v___jp_587_;
}
}
else
{
size_t v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_usize_of_nat(v___x_639_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__5(v___x_638_, v___x_637_, v___x_644_, v___x_633_);
lean_dec_ref(v___x_638_);
v___y_588_ = v___x_645_;
goto v___jp_587_;
}
}
v___jp_587_:
{
size_t v_sz_589_; lean_object* v_resultSnap_590_; lean_object* v___x_591_; lean_object* v_cmdState_592_; lean_object* v_infoState_593_; lean_object* v_env_594_; lean_object* v_scopes_595_; lean_object* v_usedQuotCtxts_596_; lean_object* v_nextMacroScope_597_; lean_object* v_maxRecDepth_598_; lean_object* v_ngen_599_; lean_object* v_auxDeclNGen_600_; lean_object* v_traceState_601_; lean_object* v_snapshotTasks_602_; lean_object* v_prevLinterStates_603_; lean_object* v_codeQualityEntryTasks_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_631_; 
v_sz_589_ = lean_array_size(v_commands_582_);
v_resultSnap_590_ = lean_ctor_get(v_elabSnap_580_, 2);
lean_inc_ref(v_resultSnap_590_);
lean_dec_ref(v_elabSnap_580_);
v___x_591_ = l_Lean_Language_SnapshotTask_get___redArg(v_resultSnap_590_);
v_cmdState_592_ = lean_ctor_get(v___x_591_, 1);
lean_inc_ref(v_cmdState_592_);
lean_dec(v___x_591_);
v_infoState_593_ = lean_ctor_get(v_cmdState_592_, 8);
v_env_594_ = lean_ctor_get(v_cmdState_592_, 0);
v_scopes_595_ = lean_ctor_get(v_cmdState_592_, 2);
v_usedQuotCtxts_596_ = lean_ctor_get(v_cmdState_592_, 3);
v_nextMacroScope_597_ = lean_ctor_get(v_cmdState_592_, 4);
v_maxRecDepth_598_ = lean_ctor_get(v_cmdState_592_, 5);
v_ngen_599_ = lean_ctor_get(v_cmdState_592_, 6);
v_auxDeclNGen_600_ = lean_ctor_get(v_cmdState_592_, 7);
v_traceState_601_ = lean_ctor_get(v_cmdState_592_, 9);
v_snapshotTasks_602_ = lean_ctor_get(v_cmdState_592_, 10);
v_prevLinterStates_603_ = lean_ctor_get(v_cmdState_592_, 11);
v_codeQualityEntryTasks_604_ = lean_ctor_get(v_cmdState_592_, 12);
v_isSharedCheck_631_ = !lean_is_exclusive(v_cmdState_592_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_cmdState_592_, 1);
lean_dec(v_unused_632_);
v___x_606_ = v_cmdState_592_;
v_isShared_607_ = v_isSharedCheck_631_;
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
lean_dec(v_cmdState_592_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_631_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
uint8_t v_enabled_608_; lean_object* v_assignment_609_; lean_object* v_lazyAssignment_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_629_; 
v_enabled_608_ = lean_ctor_get_uint8(v_infoState_593_, sizeof(void*)*3);
v_assignment_609_ = lean_ctor_get(v_infoState_593_, 0);
v_lazyAssignment_610_ = lean_ctor_get(v_infoState_593_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_infoState_593_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_infoState_593_, 2);
lean_dec(v_unused_630_);
v___x_612_ = v_infoState_593_;
v_isShared_613_ = v_isSharedCheck_629_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_lazyAssignment_610_);
lean_inc(v_assignment_609_);
lean_dec(v_infoState_593_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_629_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_pos_614_; size_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_trees_619_; lean_object* v___x_621_; 
v_pos_614_ = lean_ctor_get(v_parserState_579_, 0);
lean_inc(v_pos_614_);
v___x_615_ = ((size_t)0ULL);
lean_inc_ref(v_commands_582_);
v___x_616_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__0(v_sz_589_, v___x_615_, v_commands_582_);
v___x_617_ = lean_array_get_size(v___x_616_);
v___x_618_ = l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1(v___x_616_, v___x_586_, v___x_617_);
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
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_assignment_609_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_lazyAssignment_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_trees_619_);
lean_ctor_set_uint8(v_reuseFailAlloc_628_, sizeof(void*)*3, v_enabled_608_);
v___x_621_ = v_reuseFailAlloc_628_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_623_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 8, v___x_621_);
lean_ctor_set(v___x_606_, 1, v___y_588_);
v___x_623_ = v___x_606_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_env_594_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___y_588_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_scopes_595_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_usedQuotCtxts_596_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_nextMacroScope_597_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_maxRecDepth_598_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_ngen_599_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_auxDeclNGen_600_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_627_, 9, v_traceState_601_);
lean_ctor_set(v_reuseFailAlloc_627_, 10, v_snapshotTasks_602_);
lean_ctor_set(v_reuseFailAlloc_627_, 11, v_prevLinterStates_603_);
lean_ctor_set(v_reuseFailAlloc_627_, 12, v_codeQualityEntryTasks_604_);
v___x_623_ = v_reuseFailAlloc_627_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__2(v_sz_589_, v___x_615_, v_commands_582_);
v___x_625_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v_parserState_579_);
lean_ctor_set(v___x_625_, 2, v_pos_614_);
lean_ctor_set(v___x_625_, 3, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_inputCtx_573_);
lean_ctor_set(v___x_626_, 2, v_initialSnap_574_);
return v___x_626_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___boxed(lean_object* v_inputCtx_646_, lean_object* v_initialSnap_647_, lean_object* v_t_648_, lean_object* v_commands_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_646_, v_initialSnap_647_, v_t_648_, v_commands_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally(lean_object* v_inputCtx_654_, lean_object* v_parserState_655_, lean_object* v_commandState_656_, lean_object* v_old_x3f_657_){
_start:
{
lean_object* v___y_660_; 
if (lean_obj_tag(v_old_x3f_657_) == 0)
{
lean_object* v___x_665_; 
v___x_665_ = lean_box(0);
v___y_660_ = v___x_665_;
goto v___jp_659_;
}
else
{
lean_object* v_val_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
v_val_666_ = lean_ctor_get(v_old_x3f_657_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_old_x3f_657_);
if (v_isSharedCheck_676_ == 0)
{
v___x_668_ = v_old_x3f_657_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_val_666_);
lean_dec(v_old_x3f_657_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_inputCtx_670_; lean_object* v_initialSnap_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v_inputCtx_670_ = lean_ctor_get(v_val_666_, 1);
lean_inc_ref(v_inputCtx_670_);
v_initialSnap_671_ = lean_ctor_get(v_val_666_, 2);
lean_inc_ref(v_initialSnap_671_);
lean_dec(v_val_666_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_inputCtx_670_);
lean_ctor_set(v___x_672_, 1, v_initialSnap_671_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_672_);
v___x_674_ = v___x_668_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
v___y_660_ = v___x_674_;
goto v___jp_659_;
}
}
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = l_Lean_Language_Lean_processCommands(v_inputCtx_654_, v_parserState_655_, v_commandState_656_, v___y_660_);
lean_inc_ref(v___x_661_);
v___x_662_ = lean_task_get_own(v___x_661_);
v___x_663_ = ((lean_object*)(l_Lean_Elab_IO_processCommandsIncrementally___closed__0));
v___x_664_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go(v_inputCtx_654_, v___x_662_, v___x_661_, v___x_663_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommandsIncrementally___boxed(lean_object* v_inputCtx_677_, lean_object* v_parserState_678_, lean_object* v_commandState_679_, lean_object* v_old_x3f_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_677_, v_parserState_678_, v_commandState_679_, v_old_x3f_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands(lean_object* v_inputCtx_683_, lean_object* v_parserState_684_, lean_object* v_commandState_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_toState_689_; lean_object* v___x_690_; 
v___x_687_ = lean_box(0);
v___x_688_ = l_Lean_Elab_IO_processCommandsIncrementally(v_inputCtx_683_, v_parserState_684_, v_commandState_685_, v___x_687_);
v_toState_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc_ref(v_toState_689_);
lean_dec_ref(v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v_toState_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_IO_processCommands___boxed(lean_object* v_inputCtx_691_, lean_object* v_parserState_692_, lean_object* v_commandState_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_IO_processCommands(v_inputCtx_691_, v_parserState_692_, v_commandState_693_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process(lean_object* v_input_701_, lean_object* v_env_702_, lean_object* v_opts_703_, lean_object* v_fileName_704_){
_start:
{
lean_object* v___y_707_; 
if (lean_obj_tag(v_fileName_704_) == 0)
{
lean_object* v___x_727_; 
v___x_727_ = ((lean_object*)(l_Lean_Elab_process___closed__1));
v___y_707_ = v___x_727_;
goto v___jp_706_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v_fileName_704_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v_fileName_704_, 1);
v___y_707_ = v_val_728_;
goto v___jp_706_;
}
v___jp_706_:
{
uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v_inputCtx_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_726_; 
v___x_708_ = 1;
v___x_709_ = lean_string_utf8_byte_size(v_input_701_);
v_inputCtx_710_ = l_Lean_Parser_mkInputContext___redArg(v_input_701_, v___y_707_, v___x_708_, v___x_709_);
v___x_711_ = ((lean_object*)(l_Lean_Elab_process___closed__0));
v___x_712_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go___closed__2);
v___x_713_ = l_Lean_Elab_Command_mkState(v_env_702_, v___x_712_, v_opts_703_);
v___x_714_ = l_Lean_Elab_IO_processCommands(v_inputCtx_710_, v___x_711_, v___x_713_);
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_726_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_commandState_719_; lean_object* v_env_720_; lean_object* v_messages_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v_commandState_719_ = lean_ctor_get(v_a_715_, 0);
lean_inc_ref(v_commandState_719_);
lean_dec(v_a_715_);
v_env_720_ = lean_ctor_get(v_commandState_719_, 0);
lean_inc_ref(v_env_720_);
v_messages_721_ = lean_ctor_get(v_commandState_719_, 1);
lean_inc_ref(v_messages_721_);
lean_dec_ref(v_commandState_719_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_env_720_);
lean_ctor_set(v___x_722_, 1, v_messages_721_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_722_);
v___x_724_ = v___x_717_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_process___boxed(lean_object* v_input_729_, lean_object* v_env_730_, lean_object* v_opts_731_, lean_object* v_fileName_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Elab_process(v_input_729_, v_env_730_, v_opts_731_, v_fileName_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(lean_object* v_t_735_, lean_object* v_cmdStx_x3f_736_, lean_object* v_acc_737_){
_start:
{
lean_object* v_element_738_; lean_object* v_diagnostics_739_; lean_object* v_children_740_; lean_object* v_msgLog_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_759_; 
v_element_738_ = lean_ctor_get(v_t_735_, 0);
v_diagnostics_739_ = lean_ctor_get(v_element_738_, 1);
lean_inc_ref(v_diagnostics_739_);
v_children_740_ = lean_ctor_get(v_t_735_, 1);
lean_inc_ref(v_children_740_);
lean_dec_ref(v_t_735_);
v_msgLog_741_ = lean_ctor_get(v_diagnostics_739_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v_diagnostics_739_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v_diagnostics_739_, 1);
lean_dec(v_unused_760_);
v___x_743_ = v_diagnostics_739_;
v_isShared_744_ = v_isSharedCheck_759_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_msgLog_741_);
lean_dec(v_diagnostics_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_759_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
lean_inc(v_cmdStx_x3f_736_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v_msgLog_741_);
lean_ctor_set(v___x_743_, 0, v_cmdStx_x3f_736_);
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_cmdStx_x3f_736_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_msgLog_741_);
v___x_746_ = v_reuseFailAlloc_758_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v_acc_747_; lean_object* v___x_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_acc_747_ = lean_array_push(v_acc_737_, v___x_746_);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_array_get_size(v_children_740_);
v___x_750_ = lean_nat_dec_lt(v___x_748_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec_ref(v_children_740_);
lean_dec(v_cmdStx_x3f_736_);
return v_acc_747_;
}
else
{
uint8_t v___x_751_; 
v___x_751_ = lean_nat_dec_le(v___x_749_, v___x_749_);
if (v___x_751_ == 0)
{
if (v___x_750_ == 0)
{
lean_dec_ref(v_children_740_);
lean_dec(v_cmdStx_x3f_736_);
return v_acc_747_;
}
else
{
size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_749_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_736_, v_children_740_, v___x_752_, v___x_753_, v_acc_747_);
lean_dec_ref(v_children_740_);
return v___x_754_;
}
}
else
{
size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_749_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_736_, v_children_740_, v___x_755_, v___x_756_, v_acc_747_);
lean_dec_ref(v_children_740_);
return v___x_757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(lean_object* v_cmdStx_x3f_761_, lean_object* v_as_762_, size_t v_i_763_, size_t v_stop_764_, lean_object* v_b_765_){
_start:
{
lean_object* v___y_767_; uint8_t v___x_771_; 
v___x_771_ = lean_usize_dec_eq(v_i_763_, v_stop_764_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v_stx_x3f_773_; lean_object* v___x_774_; 
v___x_772_ = lean_array_uget_borrowed(v_as_762_, v_i_763_);
v_stx_x3f_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v___x_772_);
v___x_774_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_772_);
if (lean_obj_tag(v_stx_x3f_773_) == 0)
{
lean_object* v___x_775_; 
lean_inc(v_cmdStx_x3f_761_);
v___x_775_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_774_, v_cmdStx_x3f_761_, v_b_765_);
v___y_767_ = v___x_775_;
goto v___jp_766_;
}
else
{
lean_object* v___x_776_; 
lean_inc_ref(v_stx_x3f_773_);
v___x_776_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___x_774_, v_stx_x3f_773_, v_b_765_);
v___y_767_ = v___x_776_;
goto v___jp_766_;
}
}
else
{
lean_dec(v_cmdStx_x3f_761_);
return v_b_765_;
}
v___jp_766_:
{
size_t v___x_768_; size_t v___x_769_; 
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_add(v_i_763_, v___x_768_);
v_i_763_ = v___x_769_;
v_b_765_ = v___y_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0___boxed(lean_object* v_cmdStx_x3f_777_, lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_){
_start:
{
size_t v_i_boxed_782_; size_t v_stop_boxed_783_; lean_object* v_res_784_; 
v_i_boxed_782_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_783_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints_spec__0(v_cmdStx_x3f_777_, v_as_778_, v_i_boxed_782_, v_stop_boxed_783_, v_b_781_);
lean_dec_ref(v_as_778_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3(lean_object* v_filePath_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_lean_x3f_787_; lean_object* v_olean_x3f_788_; lean_object* v_oleanServer_x3f_789_; lean_object* v_ilean_x3f_790_; lean_object* v_irSig_x3f_791_; lean_object* v_ir_x3f_792_; lean_object* v_c_x3f_793_; lean_object* v_bc_x3f_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_lean_x3f_787_ = lean_ctor_get(v_a_786_, 0);
v_olean_x3f_788_ = lean_ctor_get(v_a_786_, 1);
v_oleanServer_x3f_789_ = lean_ctor_get(v_a_786_, 2);
v_ilean_x3f_790_ = lean_ctor_get(v_a_786_, 4);
v_irSig_x3f_791_ = lean_ctor_get(v_a_786_, 5);
v_ir_x3f_792_ = lean_ctor_get(v_a_786_, 6);
v_c_x3f_793_ = lean_ctor_get(v_a_786_, 7);
v_bc_x3f_794_ = lean_ctor_get(v_a_786_, 8);
v_isSharedCheck_802_ = !lean_is_exclusive(v_a_786_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_a_786_, 3);
lean_dec(v_unused_803_);
v___x_796_ = v_a_786_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_bc_x3f_794_);
lean_inc(v_c_x3f_793_);
lean_inc(v_ir_x3f_792_);
lean_inc(v_irSig_x3f_791_);
lean_inc(v_ilean_x3f_790_);
lean_inc(v_oleanServer_x3f_789_);
lean_inc(v_olean_x3f_788_);
lean_inc(v_lean_x3f_787_);
lean_dec(v_a_786_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_798_, 0, v_filePath_785_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 3, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_lean_x3f_787_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_olean_x3f_788_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_oleanServer_x3f_789_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_ilean_x3f_790_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_irSig_x3f_791_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_ir_x3f_792_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_c_x3f_793_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v_bc_x3f_794_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1(lean_object* v_filePath_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_lean_x3f_806_; lean_object* v_olean_x3f_807_; lean_object* v_oleanServer_x3f_808_; lean_object* v_oleanPrivate_x3f_809_; lean_object* v_ilean_x3f_810_; lean_object* v_ir_x3f_811_; lean_object* v_c_x3f_812_; lean_object* v_bc_x3f_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
v_lean_x3f_806_ = lean_ctor_get(v_a_805_, 0);
v_olean_x3f_807_ = lean_ctor_get(v_a_805_, 1);
v_oleanServer_x3f_808_ = lean_ctor_get(v_a_805_, 2);
v_oleanPrivate_x3f_809_ = lean_ctor_get(v_a_805_, 3);
v_ilean_x3f_810_ = lean_ctor_get(v_a_805_, 4);
v_ir_x3f_811_ = lean_ctor_get(v_a_805_, 6);
v_c_x3f_812_ = lean_ctor_get(v_a_805_, 7);
v_bc_x3f_813_ = lean_ctor_get(v_a_805_, 8);
v_isSharedCheck_821_ = !lean_is_exclusive(v_a_805_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_a_805_, 5);
lean_dec(v_unused_822_);
v___x_815_ = v_a_805_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_bc_x3f_813_);
lean_inc(v_c_x3f_812_);
lean_inc(v_ir_x3f_811_);
lean_inc(v_ilean_x3f_810_);
lean_inc(v_oleanPrivate_x3f_809_);
lean_inc(v_oleanServer_x3f_808_);
lean_inc(v_olean_x3f_807_);
lean_inc(v_lean_x3f_806_);
lean_dec(v_a_805_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_817_, 0, v_filePath_804_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 5, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_lean_x3f_806_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_olean_x3f_807_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_oleanServer_x3f_808_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_oleanPrivate_x3f_809_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_ilean_x3f_810_);
lean_ctor_set(v_reuseFailAlloc_820_, 5, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 6, v_ir_x3f_811_);
lean_ctor_set(v_reuseFailAlloc_820_, 7, v_c_x3f_812_);
lean_ctor_set(v_reuseFailAlloc_820_, 8, v_bc_x3f_813_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4(lean_object* v_filePath_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_lean_x3f_825_; lean_object* v_olean_x3f_826_; lean_object* v_oleanPrivate_x3f_827_; lean_object* v_ilean_x3f_828_; lean_object* v_irSig_x3f_829_; lean_object* v_ir_x3f_830_; lean_object* v_c_x3f_831_; lean_object* v_bc_x3f_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_840_; 
v_lean_x3f_825_ = lean_ctor_get(v_a_824_, 0);
v_olean_x3f_826_ = lean_ctor_get(v_a_824_, 1);
v_oleanPrivate_x3f_827_ = lean_ctor_get(v_a_824_, 3);
v_ilean_x3f_828_ = lean_ctor_get(v_a_824_, 4);
v_irSig_x3f_829_ = lean_ctor_get(v_a_824_, 5);
v_ir_x3f_830_ = lean_ctor_get(v_a_824_, 6);
v_c_x3f_831_ = lean_ctor_get(v_a_824_, 7);
v_bc_x3f_832_ = lean_ctor_get(v_a_824_, 8);
v_isSharedCheck_840_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v_a_824_, 2);
lean_dec(v_unused_841_);
v___x_834_ = v_a_824_;
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_bc_x3f_832_);
lean_inc(v_c_x3f_831_);
lean_inc(v_ir_x3f_830_);
lean_inc(v_irSig_x3f_829_);
lean_inc(v_ilean_x3f_828_);
lean_inc(v_oleanPrivate_x3f_827_);
lean_inc(v_olean_x3f_826_);
lean_inc(v_lean_x3f_825_);
lean_dec(v_a_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v_filePath_823_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 2, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_lean_x3f_825_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_olean_x3f_826_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_839_, 3, v_oleanPrivate_x3f_827_);
lean_ctor_set(v_reuseFailAlloc_839_, 4, v_ilean_x3f_828_);
lean_ctor_set(v_reuseFailAlloc_839_, 5, v_irSig_x3f_829_);
lean_ctor_set(v_reuseFailAlloc_839_, 6, v_ir_x3f_830_);
lean_ctor_set(v_reuseFailAlloc_839_, 7, v_c_x3f_831_);
lean_ctor_set(v_reuseFailAlloc_839_, 8, v_bc_x3f_832_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_843_) == 0)
{
uint8_t v___x_844_; 
v___x_844_ = 0;
return v___x_844_;
}
else
{
lean_object* v_key_845_; lean_object* v_tail_846_; uint8_t v___x_847_; 
v_key_845_ = lean_ctor_get(v_x_843_, 0);
v_tail_846_ = lean_ctor_get(v_x_843_, 2);
v___x_847_ = lean_string_dec_eq(v_key_845_, v_a_842_);
if (v___x_847_ == 0)
{
v_x_843_ = v_tail_846_;
goto _start;
}
else
{
return v___x_847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg___boxed(lean_object* v_a_849_, lean_object* v_x_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_849_, v_x_850_);
lean_dec(v_x_850_);
lean_dec_ref(v_a_849_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(lean_object* v_m_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_buckets_855_; lean_object* v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v___x_859_; uint64_t v_fold_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_buckets_855_ = lean_ctor_get(v_m_853_, 1);
v___x_856_ = lean_array_get_size(v_buckets_855_);
v___x_857_ = lean_string_hash(v_a_854_);
v___x_858_ = 32ULL;
v___x_859_ = lean_uint64_shift_right(v___x_857_, v___x_858_);
v_fold_860_ = lean_uint64_xor(v___x_857_, v___x_859_);
v___x_861_ = 16ULL;
v___x_862_ = lean_uint64_shift_right(v_fold_860_, v___x_861_);
v___x_863_ = lean_uint64_xor(v_fold_860_, v___x_862_);
v___x_864_ = lean_uint64_to_usize(v___x_863_);
v___x_865_ = lean_usize_of_nat(v___x_856_);
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_sub(v___x_865_, v___x_866_);
v___x_868_ = lean_usize_land(v___x_864_, v___x_867_);
v___x_869_ = lean_array_uget_borrowed(v_buckets_855_, v___x_868_);
v___x_870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_854_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg___boxed(lean_object* v_m_871_, lean_object* v_a_872_){
_start:
{
uint8_t v_res_873_; lean_object* v_r_874_; 
v_res_873_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_871_, v_a_872_);
lean_dec_ref(v_a_872_);
lean_dec_ref(v_m_871_);
v_r_874_ = lean_box(v_res_873_);
return v_r_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(lean_object* v_a_875_, lean_object* v_fallback_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_inc(v_fallback_876_);
return v_fallback_876_;
}
else
{
lean_object* v_key_878_; lean_object* v_value_879_; lean_object* v_tail_880_; uint8_t v___x_881_; 
v_key_878_ = lean_ctor_get(v_x_877_, 0);
v_value_879_ = lean_ctor_get(v_x_877_, 1);
v_tail_880_ = lean_ctor_get(v_x_877_, 2);
v___x_881_ = lean_string_dec_eq(v_key_878_, v_a_875_);
if (v___x_881_ == 0)
{
v_x_877_ = v_tail_880_;
goto _start;
}
else
{
lean_inc(v_value_879_);
return v_value_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg___boxed(lean_object* v_a_883_, lean_object* v_fallback_884_, lean_object* v_x_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_883_, v_fallback_884_, v_x_885_);
lean_dec(v_x_885_);
lean_dec(v_fallback_884_);
lean_dec_ref(v_a_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(lean_object* v_m_887_, lean_object* v_a_888_, lean_object* v_fallback_889_){
_start:
{
lean_object* v_buckets_890_; lean_object* v___x_891_; uint64_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v_fold_895_; uint64_t v___x_896_; uint64_t v___x_897_; uint64_t v___x_898_; size_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_buckets_890_ = lean_ctor_get(v_m_887_, 1);
v___x_891_ = lean_array_get_size(v_buckets_890_);
v___x_892_ = lean_string_hash(v_a_888_);
v___x_893_ = 32ULL;
v___x_894_ = lean_uint64_shift_right(v___x_892_, v___x_893_);
v_fold_895_ = lean_uint64_xor(v___x_892_, v___x_894_);
v___x_896_ = 16ULL;
v___x_897_ = lean_uint64_shift_right(v_fold_895_, v___x_896_);
v___x_898_ = lean_uint64_xor(v_fold_895_, v___x_897_);
v___x_899_ = lean_uint64_to_usize(v___x_898_);
v___x_900_ = lean_usize_of_nat(v___x_891_);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_sub(v___x_900_, v___x_901_);
v___x_903_ = lean_usize_land(v___x_899_, v___x_902_);
v___x_904_ = lean_array_uget_borrowed(v_buckets_890_, v___x_903_);
v___x_905_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_888_, v_fallback_889_, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg___boxed(lean_object* v_m_906_, lean_object* v_a_907_, lean_object* v_fallback_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_906_, v_a_907_, v_fallback_908_);
lean_dec(v_fallback_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_m_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2(lean_object* v_filePath_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_lean_x3f_912_; lean_object* v_olean_x3f_913_; lean_object* v_oleanServer_x3f_914_; lean_object* v_oleanPrivate_x3f_915_; lean_object* v_ilean_x3f_916_; lean_object* v_irSig_x3f_917_; lean_object* v_c_x3f_918_; lean_object* v_bc_x3f_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_927_; 
v_lean_x3f_912_ = lean_ctor_get(v_a_911_, 0);
v_olean_x3f_913_ = lean_ctor_get(v_a_911_, 1);
v_oleanServer_x3f_914_ = lean_ctor_get(v_a_911_, 2);
v_oleanPrivate_x3f_915_ = lean_ctor_get(v_a_911_, 3);
v_ilean_x3f_916_ = lean_ctor_get(v_a_911_, 4);
v_irSig_x3f_917_ = lean_ctor_get(v_a_911_, 5);
v_c_x3f_918_ = lean_ctor_get(v_a_911_, 7);
v_bc_x3f_919_ = lean_ctor_get(v_a_911_, 8);
v_isSharedCheck_927_ = !lean_is_exclusive(v_a_911_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v_a_911_, 6);
lean_dec(v_unused_928_);
v___x_921_ = v_a_911_;
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_bc_x3f_919_);
lean_inc(v_c_x3f_918_);
lean_inc(v_irSig_x3f_917_);
lean_inc(v_ilean_x3f_916_);
lean_inc(v_oleanPrivate_x3f_915_);
lean_inc(v_oleanServer_x3f_914_);
lean_inc(v_olean_x3f_913_);
lean_inc(v_lean_x3f_912_);
lean_dec(v_a_911_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_filePath_910_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 6, v___x_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_lean_x3f_912_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_olean_x3f_913_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_oleanServer_x3f_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_oleanPrivate_x3f_915_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v_ilean_x3f_916_);
lean_ctor_set(v_reuseFailAlloc_926_, 5, v_irSig_x3f_917_);
lean_ctor_set(v_reuseFailAlloc_926_, 6, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_926_, 7, v_c_x3f_918_);
lean_ctor_set(v_reuseFailAlloc_926_, 8, v_bc_x3f_919_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0(lean_object* v_filePath_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_lean_x3f_931_; lean_object* v_oleanServer_x3f_932_; lean_object* v_oleanPrivate_x3f_933_; lean_object* v_ilean_x3f_934_; lean_object* v_irSig_x3f_935_; lean_object* v_ir_x3f_936_; lean_object* v_c_x3f_937_; lean_object* v_bc_x3f_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_946_; 
v_lean_x3f_931_ = lean_ctor_get(v_a_930_, 0);
v_oleanServer_x3f_932_ = lean_ctor_get(v_a_930_, 2);
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
v_unused_947_ = lean_ctor_get(v_a_930_, 1);
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
lean_inc(v_oleanServer_x3f_932_);
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
lean_ctor_set(v___x_940_, 1, v___x_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_lean_x3f_931_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_oleanServer_x3f_932_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(lean_object* v_a_948_, lean_object* v_b_949_, lean_object* v_x_950_){
_start:
{
if (lean_obj_tag(v_x_950_) == 0)
{
lean_dec(v_b_949_);
lean_dec_ref(v_a_948_);
return v_x_950_;
}
else
{
lean_object* v_key_951_; lean_object* v_value_952_; lean_object* v_tail_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_965_; 
v_key_951_ = lean_ctor_get(v_x_950_, 0);
v_value_952_ = lean_ctor_get(v_x_950_, 1);
v_tail_953_ = lean_ctor_get(v_x_950_, 2);
v_isSharedCheck_965_ = !lean_is_exclusive(v_x_950_);
if (v_isSharedCheck_965_ == 0)
{
v___x_955_ = v_x_950_;
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_tail_953_);
lean_inc(v_value_952_);
lean_inc(v_key_951_);
lean_dec(v_x_950_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_965_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
uint8_t v___x_957_; 
v___x_957_ = lean_string_dec_eq(v_key_951_, v_a_948_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_948_, v_b_949_, v_tail_953_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 2, v___x_958_);
v___x_960_ = v___x_955_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_key_951_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_value_952_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
else
{
lean_object* v___x_963_; 
lean_dec(v_value_952_);
lean_dec(v_key_951_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v_b_949_);
lean_ctor_set(v___x_955_, 0, v_a_948_);
v___x_963_ = v___x_955_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_948_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_b_949_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_tail_953_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_x_967_) == 0)
{
return v_x_966_;
}
else
{
lean_object* v_key_968_; lean_object* v_value_969_; lean_object* v_tail_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_993_; 
v_key_968_ = lean_ctor_get(v_x_967_, 0);
v_value_969_ = lean_ctor_get(v_x_967_, 1);
v_tail_970_ = lean_ctor_get(v_x_967_, 2);
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_967_);
if (v_isSharedCheck_993_ == 0)
{
v___x_972_ = v_x_967_;
v_isShared_973_ = v_isSharedCheck_993_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_tail_970_);
lean_inc(v_value_969_);
lean_inc(v_key_968_);
lean_dec(v_x_967_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_993_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; uint64_t v___x_975_; uint64_t v___x_976_; uint64_t v___x_977_; uint64_t v_fold_978_; uint64_t v___x_979_; uint64_t v___x_980_; uint64_t v___x_981_; size_t v___x_982_; size_t v___x_983_; size_t v___x_984_; size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_974_ = lean_array_get_size(v_x_966_);
v___x_975_ = lean_string_hash(v_key_968_);
v___x_976_ = 32ULL;
v___x_977_ = lean_uint64_shift_right(v___x_975_, v___x_976_);
v_fold_978_ = lean_uint64_xor(v___x_975_, v___x_977_);
v___x_979_ = 16ULL;
v___x_980_ = lean_uint64_shift_right(v_fold_978_, v___x_979_);
v___x_981_ = lean_uint64_xor(v_fold_978_, v___x_980_);
v___x_982_ = lean_uint64_to_usize(v___x_981_);
v___x_983_ = lean_usize_of_nat(v___x_974_);
v___x_984_ = ((size_t)1ULL);
v___x_985_ = lean_usize_sub(v___x_983_, v___x_984_);
v___x_986_ = lean_usize_land(v___x_982_, v___x_985_);
v___x_987_ = lean_array_uget_borrowed(v_x_966_, v___x_986_);
lean_inc(v___x_987_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 2, v___x_987_);
v___x_989_ = v___x_972_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_key_968_);
lean_ctor_set(v_reuseFailAlloc_992_, 1, v_value_969_);
lean_ctor_set(v_reuseFailAlloc_992_, 2, v___x_987_);
v___x_989_ = v_reuseFailAlloc_992_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; 
v___x_990_ = lean_array_uset(v_x_966_, v___x_986_, v___x_989_);
v_x_966_ = v___x_990_;
v_x_967_ = v_tail_970_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(lean_object* v_i_994_, lean_object* v_source_995_, lean_object* v_target_996_){
_start:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_array_get_size(v_source_995_);
v___x_998_ = lean_nat_dec_lt(v_i_994_, v___x_997_);
if (v___x_998_ == 0)
{
lean_dec_ref(v_source_995_);
lean_dec(v_i_994_);
return v_target_996_;
}
else
{
lean_object* v_es_999_; lean_object* v___x_1000_; lean_object* v_source_1001_; lean_object* v_target_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_es_999_ = lean_array_fget(v_source_995_, v_i_994_);
v___x_1000_ = lean_box(0);
v_source_1001_ = lean_array_fset(v_source_995_, v_i_994_, v___x_1000_);
v_target_1002_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_target_996_, v_es_999_);
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_i_994_, v___x_1003_);
lean_dec(v_i_994_);
v_i_994_ = v___x_1004_;
v_source_995_ = v_source_1001_;
v_target_996_ = v_target_1002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(lean_object* v_data_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_nbuckets_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1007_ = lean_array_get_size(v_data_1006_);
v___x_1008_ = lean_unsigned_to_nat(2u);
v_nbuckets_1009_ = lean_nat_mul(v___x_1007_, v___x_1008_);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_mk_array(v_nbuckets_1009_, v___x_1011_);
v___x_1013_ = lean_array_propagate_mark(v_data_1006_, v___x_1012_);
v___x_1014_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v___x_1010_, v_data_1006_, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(lean_object* v_m_1015_, lean_object* v_a_1016_, lean_object* v_b_1017_){
_start:
{
lean_object* v_size_1018_; lean_object* v_buckets_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1062_; 
v_size_1018_ = lean_ctor_get(v_m_1015_, 0);
v_buckets_1019_ = lean_ctor_get(v_m_1015_, 1);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_m_1015_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1021_ = v_m_1015_;
v_isShared_1022_ = v_isSharedCheck_1062_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_buckets_1019_);
lean_inc(v_size_1018_);
lean_dec(v_m_1015_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1062_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; uint64_t v___x_1024_; uint64_t v___x_1025_; uint64_t v___x_1026_; uint64_t v_fold_1027_; uint64_t v___x_1028_; uint64_t v___x_1029_; uint64_t v___x_1030_; size_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; lean_object* v_bkt_1036_; uint8_t v___x_1037_; 
v___x_1023_ = lean_array_get_size(v_buckets_1019_);
v___x_1024_ = lean_string_hash(v_a_1016_);
v___x_1025_ = 32ULL;
v___x_1026_ = lean_uint64_shift_right(v___x_1024_, v___x_1025_);
v_fold_1027_ = lean_uint64_xor(v___x_1024_, v___x_1026_);
v___x_1028_ = 16ULL;
v___x_1029_ = lean_uint64_shift_right(v_fold_1027_, v___x_1028_);
v___x_1030_ = lean_uint64_xor(v_fold_1027_, v___x_1029_);
v___x_1031_ = lean_uint64_to_usize(v___x_1030_);
v___x_1032_ = lean_usize_of_nat(v___x_1023_);
v___x_1033_ = ((size_t)1ULL);
v___x_1034_ = lean_usize_sub(v___x_1032_, v___x_1033_);
v___x_1035_ = lean_usize_land(v___x_1031_, v___x_1034_);
v_bkt_1036_ = lean_array_uget_borrowed(v_buckets_1019_, v___x_1035_);
v___x_1037_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1016_, v_bkt_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v_size_x27_1039_; lean_object* v___x_1040_; lean_object* v_buckets_x27_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1038_ = lean_unsigned_to_nat(1u);
v_size_x27_1039_ = lean_nat_add(v_size_1018_, v___x_1038_);
lean_dec(v_size_1018_);
lean_inc(v_bkt_1036_);
v___x_1040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1040_, 0, v_a_1016_);
lean_ctor_set(v___x_1040_, 1, v_b_1017_);
lean_ctor_set(v___x_1040_, 2, v_bkt_1036_);
v_buckets_x27_1041_ = lean_array_uset(v_buckets_1019_, v___x_1035_, v___x_1040_);
v___x_1042_ = lean_unsigned_to_nat(4u);
v___x_1043_ = lean_nat_mul(v_size_x27_1039_, v___x_1042_);
v___x_1044_ = lean_unsigned_to_nat(3u);
v___x_1045_ = lean_nat_div(v___x_1043_, v___x_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_array_get_size(v_buckets_x27_1041_);
v___x_1047_ = lean_nat_dec_le(v___x_1045_, v___x_1046_);
lean_dec(v___x_1045_);
if (v___x_1047_ == 0)
{
lean_object* v_val_1048_; lean_object* v___x_1050_; 
v_val_1048_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_buckets_x27_1041_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v_val_1048_);
lean_ctor_set(v___x_1021_, 0, v_size_x27_1039_);
v___x_1050_ = v___x_1021_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_size_x27_1039_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_val_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
else
{
lean_object* v___x_1053_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v_buckets_x27_1041_);
lean_ctor_set(v___x_1021_, 0, v_size_x27_1039_);
v___x_1053_ = v___x_1021_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_size_x27_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_buckets_x27_1041_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
else
{
lean_object* v___x_1055_; lean_object* v_buckets_x27_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
lean_inc(v_bkt_1036_);
v___x_1055_ = lean_box(0);
v_buckets_x27_1056_ = lean_array_uset(v_buckets_1019_, v___x_1035_, v___x_1055_);
v___x_1057_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1016_, v_b_1017_, v_bkt_1036_);
v___x_1058_ = lean_array_uset(v_buckets_x27_1056_, v___x_1035_, v___x_1057_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 1, v___x_1058_);
v___x_1060_ = v___x_1021_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_size_1018_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(lean_object* v_as_1071_, size_t v_sz_1072_, size_t v_i_1073_, lean_object* v_b_1074_){
_start:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_usize_dec_lt(v_i_1073_, v_sz_1072_);
if (v___x_1075_ == 0)
{
return v_b_1074_;
}
else
{
lean_object* v_fst_1076_; lean_object* v_snd_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1127_; 
v_fst_1076_ = lean_ctor_get(v_b_1074_, 0);
v_snd_1077_ = lean_ctor_get(v_b_1074_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_b_1074_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1079_ = v_b_1074_;
v_isShared_1080_ = v_isSharedCheck_1127_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_snd_1077_);
lean_inc(v_fst_1076_);
lean_dec(v_b_1074_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1127_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v_order_1084_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v_a_1100_; lean_object* v_filePath_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; 
v_a_1100_ = lean_array_uget_borrowed(v_as_1071_, v_i_1073_);
v_filePath_1101_ = lean_ctor_get(v_a_1100_, 0);
lean_inc_ref_n(v_filePath_1101_, 2);
v___f_1102_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1102_, 0, v_filePath_1101_);
v___x_1103_ = l_System_FilePath_extension(v_filePath_1101_);
if (lean_obj_tag(v___x_1103_) == 1)
{
lean_object* v_val_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_val_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_val_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__1));
v___x_1106_ = lean_string_dec_eq(v_val_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__2));
v___x_1108_ = lean_string_dec_eq(v_val_1104_, v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__3));
v___x_1110_ = lean_string_dec_eq(v_val_1104_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__4));
v___x_1112_ = lean_string_dec_eq(v_val_1104_, v___x_1111_);
lean_dec(v_val_1104_);
if (v___x_1112_ == 0)
{
lean_inc_ref(v_filePath_1101_);
v_fst_1096_ = v_filePath_1101_;
v_snd_1097_ = v___f_1102_;
goto v___jp_1095_;
}
else
{
lean_object* v___f_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v___f_1102_);
lean_inc_ref_n(v_filePath_1101_, 2);
v___f_1113_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__1), 2, 1);
lean_closure_set(v___f_1113_, 0, v_filePath_1101_);
v___x_1114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1115_ = l_System_FilePath_withExtension(v_filePath_1101_, v___x_1114_);
v___x_1116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1117_ = l_System_FilePath_withExtension(v___x_1115_, v___x_1116_);
v_fst_1096_ = v___x_1117_;
v_snd_1097_ = v___f_1113_;
goto v___jp_1095_;
}
}
else
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v_val_1104_);
lean_dec_ref(v___f_1102_);
lean_inc_ref_n(v_filePath_1101_, 2);
v___f_1118_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__2), 2, 1);
lean_closure_set(v___f_1118_, 0, v_filePath_1101_);
v___x_1119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__6));
v___x_1120_ = l_System_FilePath_withExtension(v_filePath_1101_, v___x_1119_);
v_fst_1096_ = v___x_1120_;
v_snd_1097_ = v___f_1118_;
goto v___jp_1095_;
}
}
else
{
lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_val_1104_);
lean_dec_ref(v___f_1102_);
lean_inc_ref_n(v_filePath_1101_, 2);
v___f_1121_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__3), 2, 1);
lean_closure_set(v___f_1121_, 0, v_filePath_1101_);
v___x_1122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1123_ = l_System_FilePath_withExtension(v_filePath_1101_, v___x_1122_);
v_fst_1096_ = v___x_1123_;
v_snd_1097_ = v___f_1121_;
goto v___jp_1095_;
}
}
else
{
lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_val_1104_);
lean_dec_ref(v___f_1102_);
lean_inc_ref_n(v_filePath_1101_, 2);
v___f_1124_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___lam__4), 2, 1);
lean_closure_set(v___f_1124_, 0, v_filePath_1101_);
v___x_1125_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__5));
v___x_1126_ = l_System_FilePath_withExtension(v_filePath_1101_, v___x_1125_);
v_fst_1096_ = v___x_1126_;
v_snd_1097_ = v___f_1124_;
goto v___jp_1095_;
}
}
else
{
lean_dec(v___x_1103_);
lean_inc_ref(v_filePath_1101_);
v_fst_1096_ = v_filePath_1101_;
v_snd_1097_ = v___f_1102_;
goto v___jp_1095_;
}
v___jp_1081_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___closed__0));
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_snd_1077_, v___y_1082_, v___x_1085_);
v___x_1087_ = lean_apply_1(v___y_1083_, v___x_1086_);
v___x_1088_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_snd_1077_, v___y_1082_, v___x_1087_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 1, v___x_1088_);
lean_ctor_set(v___x_1079_, 0, v_order_1084_);
v___x_1090_ = v___x_1079_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_order_1084_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
size_t v___x_1091_; size_t v___x_1092_; 
v___x_1091_ = ((size_t)1ULL);
v___x_1092_ = lean_usize_add(v_i_1073_, v___x_1091_);
v_i_1073_ = v___x_1092_;
v_b_1074_ = v___x_1090_;
goto _start;
}
}
v___jp_1095_:
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_snd_1077_, v_fst_1096_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_inc_ref(v_fst_1096_);
v___x_1099_ = lean_array_push(v_fst_1076_, v_fst_1096_);
v___y_1082_ = v_fst_1096_;
v___y_1083_ = v_snd_1097_;
v_order_1084_ = v___x_1099_;
goto v___jp_1081_;
}
else
{
v___y_1082_ = v_fst_1096_;
v___y_1083_ = v_snd_1097_;
v_order_1084_ = v_fst_1076_;
goto v___jp_1081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3___boxed(lean_object* v_as_1128_, lean_object* v_sz_1129_, lean_object* v_i_1130_, lean_object* v_b_1131_){
_start:
{
size_t v_sz_boxed_1132_; size_t v_i_boxed_1133_; lean_object* v_res_1134_; 
v_sz_boxed_1132_ = lean_unbox_usize(v_sz_1129_);
lean_dec(v_sz_1129_);
v_i_boxed_1133_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_res_1134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_as_1128_, v_sz_boxed_1132_, v_i_boxed_1133_, v_b_1131_);
lean_dec_ref(v_as_1128_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(lean_object* v_msg_1135_){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1137_ = lean_panic_fn_borrowed(v___x_1136_, v_msg_1135_);
return v___x_1137_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1141_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__2));
v___x_1142_ = lean_unsigned_to_nat(11u);
v___x_1143_ = lean_unsigned_to_nat(163u);
v___x_1144_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__1));
v___x_1145_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__0));
v___x_1146_ = l_mkPanicMessageWithDecl(v___x_1145_, v___x_1144_, v___x_1143_, v___x_1142_, v___x_1141_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(lean_object* v_a_1147_, lean_object* v_x_1148_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___closed__3);
v___x_1150_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8_spec__10(v___x_1149_);
return v___x_1150_;
}
else
{
lean_object* v_key_1151_; lean_object* v_value_1152_; lean_object* v_tail_1153_; uint8_t v___x_1154_; 
v_key_1151_ = lean_ctor_get(v_x_1148_, 0);
v_value_1152_ = lean_ctor_get(v_x_1148_, 1);
v_tail_1153_ = lean_ctor_get(v_x_1148_, 2);
v___x_1154_ = lean_string_dec_eq(v_key_1151_, v_a_1147_);
if (v___x_1154_ == 0)
{
v_x_1148_ = v_tail_1153_;
goto _start;
}
else
{
lean_inc(v_value_1152_);
return v_value_1152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8___boxed(lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1156_, v_x_1157_);
lean_dec(v_x_1157_);
lean_dec_ref(v_a_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(lean_object* v_m_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_buckets_1161_; lean_object* v___x_1162_; uint64_t v___x_1163_; uint64_t v___x_1164_; uint64_t v___x_1165_; uint64_t v_fold_1166_; uint64_t v___x_1167_; uint64_t v___x_1168_; uint64_t v___x_1169_; size_t v___x_1170_; size_t v___x_1171_; size_t v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_buckets_1161_ = lean_ctor_get(v_m_1159_, 1);
v___x_1162_ = lean_array_get_size(v_buckets_1161_);
v___x_1163_ = lean_string_hash(v_a_1160_);
v___x_1164_ = 32ULL;
v___x_1165_ = lean_uint64_shift_right(v___x_1163_, v___x_1164_);
v_fold_1166_ = lean_uint64_xor(v___x_1163_, v___x_1165_);
v___x_1167_ = 16ULL;
v___x_1168_ = lean_uint64_shift_right(v_fold_1166_, v___x_1167_);
v___x_1169_ = lean_uint64_xor(v_fold_1166_, v___x_1168_);
v___x_1170_ = lean_uint64_to_usize(v___x_1169_);
v___x_1171_ = lean_usize_of_nat(v___x_1162_);
v___x_1172_ = ((size_t)1ULL);
v___x_1173_ = lean_usize_sub(v___x_1171_, v___x_1172_);
v___x_1174_ = lean_usize_land(v___x_1170_, v___x_1173_);
v___x_1175_ = lean_array_uget_borrowed(v_buckets_1161_, v___x_1174_);
v___x_1176_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4_spec__8(v_a_1160_, v___x_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4___boxed(lean_object* v_m_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v_m_1177_, v_a_1178_);
lean_dec_ref(v_a_1178_);
lean_dec_ref(v_m_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(lean_object* v___x_1180_, size_t v_sz_1181_, size_t v_i_1182_, lean_object* v_bs_1183_){
_start:
{
uint8_t v___x_1184_; 
v___x_1184_ = lean_usize_dec_lt(v_i_1182_, v_sz_1181_);
if (v___x_1184_ == 0)
{
return v_bs_1183_;
}
else
{
lean_object* v_v_1185_; lean_object* v___x_1186_; lean_object* v_bs_x27_1187_; lean_object* v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v_v_1185_ = lean_array_uget(v_bs_1183_, v_i_1182_);
v___x_1186_ = lean_unsigned_to_nat(0u);
v_bs_x27_1187_ = lean_array_uset(v_bs_1183_, v_i_1182_, v___x_1186_);
v___x_1188_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__4(v___x_1180_, v_v_1185_);
lean_dec(v_v_1185_);
v___x_1189_ = ((size_t)1ULL);
v___x_1190_ = lean_usize_add(v_i_1182_, v___x_1189_);
v___x_1191_ = lean_array_uset(v_bs_x27_1187_, v_i_1182_, v___x_1188_);
v_i_1182_ = v___x_1190_;
v_bs_1183_ = v___x_1191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5___boxed(lean_object* v___x_1193_, lean_object* v_sz_1194_, lean_object* v_i_1195_, lean_object* v_bs_1196_){
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1194_);
lean_dec(v_sz_1194_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1195_);
lean_dec(v_i_1195_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v___x_1193_, v_sz_boxed_1197_, v_i_boxed_1198_, v_bs_1196_);
lean_dec_ref(v___x_1193_);
return v_res_1199_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_box(0);
v___x_1203_ = lean_unsigned_to_nat(16u);
v___x_1204_ = lean_mk_array(v___x_1203_, v___x_1202_);
return v___x_1204_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_byBase_1207_; 
v___x_1205_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__1);
v___x_1206_ = lean_unsigned_to_nat(0u);
v_byBase_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_byBase_1207_, 0, v___x_1206_);
lean_ctor_set(v_byBase_1207_, 1, v___x_1205_);
return v_byBase_1207_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3(void){
_start:
{
lean_object* v_byBase_1208_; lean_object* v_order_1209_; lean_object* v___x_1210_; 
v_byBase_1208_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__2);
v_order_1209_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__0));
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_order_1209_);
lean_ctor_set(v___x_1210_, 1, v_byBase_1208_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(lean_object* v_regions_1211_){
_start:
{
lean_object* v___x_1212_; size_t v_sz_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v_fst_1216_; lean_object* v_snd_1217_; size_t v_sz_1218_; lean_object* v___x_1219_; 
v___x_1212_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___closed__3);
v_sz_1213_ = lean_array_size(v_regions_1211_);
v___x_1214_ = ((size_t)0ULL);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__3(v_regions_1211_, v_sz_1213_, v___x_1214_, v___x_1212_);
v_fst_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_fst_1216_);
v_snd_1217_ = lean_ctor_get(v___x_1215_, 1);
lean_inc(v_snd_1217_);
lean_dec_ref(v___x_1215_);
v_sz_1218_ = lean_array_size(v_fst_1216_);
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__5(v_snd_1217_, v_sz_1218_, v___x_1214_, v_fst_1216_);
lean_dec(v_snd_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts___boxed(lean_object* v_regions_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1220_);
lean_dec_ref(v_regions_1220_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(lean_object* v_00_u03b2_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_, lean_object* v_fallback_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___redArg(v_m_1223_, v_a_1224_, v_fallback_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0___boxed(lean_object* v_00_u03b2_1227_, lean_object* v_m_1228_, lean_object* v_a_1229_, lean_object* v_fallback_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0(v_00_u03b2_1227_, v_m_1228_, v_a_1229_, v_fallback_1230_);
lean_dec(v_fallback_1230_);
lean_dec_ref(v_a_1229_);
lean_dec_ref(v_m_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1(lean_object* v_00_u03b2_1232_, lean_object* v_m_1233_, lean_object* v_a_1234_, lean_object* v_b_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1___redArg(v_m_1233_, v_a_1234_, v_b_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(lean_object* v_00_u03b2_1237_, lean_object* v_m_1238_, lean_object* v_a_1239_){
_start:
{
uint8_t v___x_1240_; 
v___x_1240_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___redArg(v_m_1238_, v_a_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2___boxed(lean_object* v_00_u03b2_1241_, lean_object* v_m_1242_, lean_object* v_a_1243_){
_start:
{
uint8_t v_res_1244_; lean_object* v_r_1245_; 
v_res_1244_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__2(v_00_u03b2_1241_, v_m_1242_, v_a_1243_);
lean_dec_ref(v_a_1243_);
lean_dec_ref(v_m_1242_);
v_r_1245_ = lean_box(v_res_1244_);
return v_r_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(lean_object* v_00_u03b2_1246_, lean_object* v_a_1247_, lean_object* v_fallback_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___redArg(v_a_1247_, v_fallback_1248_, v_x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1251_, lean_object* v_a_1252_, lean_object* v_fallback_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__0_spec__0(v_00_u03b2_1251_, v_a_1252_, v_fallback_1253_, v_x_1254_);
lean_dec(v_x_1254_);
lean_dec(v_fallback_1253_);
lean_dec_ref(v_a_1252_);
return v_res_1255_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(lean_object* v_00_u03b2_1256_, lean_object* v_a_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___redArg(v_a_1257_, v_x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1260_, lean_object* v_a_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v_res_1263_; lean_object* v_r_1264_; 
v_res_1263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__2(v_00_u03b2_1260_, v_a_1261_, v_x_1262_);
lean_dec(v_x_1262_);
lean_dec_ref(v_a_1261_);
v_r_1264_ = lean_box(v_res_1263_);
return v_r_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3(lean_object* v_00_u03b2_1265_, lean_object* v_data_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3___redArg(v_data_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4(lean_object* v_00_u03b2_1268_, lean_object* v_a_1269_, lean_object* v_b_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__4___redArg(v_a_1269_, v_b_1270_, v_x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1273_, lean_object* v_i_1274_, lean_object* v_source_1275_, lean_object* v_target_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4___redArg(v_i_1274_, v_source_1275_, v_target_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9(lean_object* v_00_u03b2_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts_spec__1_spec__3_spec__4_spec__9___redArg(v_x_1279_, v_x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(lean_object* v_as_1282_, size_t v_sz_1283_, size_t v_i_1284_, lean_object* v_b_1285_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_usize_dec_lt(v_i_1284_, v_sz_1283_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_b_1285_);
return v___x_1288_;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1290_; 
v_a_1289_ = lean_array_uget_borrowed(v_as_1282_, v_i_1284_);
v___x_1290_ = lean_compacted_region_read(v_a_1289_, v_b_1285_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v_snd_1292_; lean_object* v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v_snd_1292_ = lean_ctor_get(v_a_1291_, 1);
lean_inc(v_snd_1292_);
lean_dec(v_a_1291_);
v___x_1293_ = lean_array_push(v_b_1285_, v_snd_1292_);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1284_, v___x_1294_);
v_i_1284_ = v___x_1295_;
v_b_1285_ = v___x_1293_;
goto _start;
}
else
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1304_; 
lean_dec_ref(v_b_1285_);
v_a_1297_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1299_ = v___x_1290_;
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1290_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1304_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1302_; 
if (v_isShared_1300_ == 0)
{
v___x_1302_ = v___x_1299_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_a_1297_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0___boxed(lean_object* v_as_1305_, lean_object* v_sz_1306_, lean_object* v_i_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1306_);
lean_dec(v_sz_1306_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1307_);
lean_dec(v_i_1307_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v_as_1305_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1308_);
lean_dec_ref(v_as_1305_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(lean_object* v_arts_1315_){
_start:
{
lean_object* v_oleanRegions_1317_; lean_object* v___x_1318_; size_t v_sz_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v_oleanRegions_1317_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc_ref(v_arts_1315_);
v___x_1318_ = l_Lean_ModuleArtifacts_oleanParts(v_arts_1315_);
v_sz_1319_ = lean_array_size(v___x_1318_);
v___x_1320_ = ((size_t)0ULL);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1318_, v_sz_1319_, v___x_1320_, v_oleanRegions_1317_);
lean_dec_ref(v___x_1318_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; size_t v_sz_1324_; lean_object* v___x_1325_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = l_Lean_ModuleArtifacts_irParts(v_arts_1315_);
v_sz_1324_ = lean_array_size(v___x_1323_);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions_spec__0(v___x_1323_, v_sz_1324_, v___x_1320_, v_oleanRegions_1317_);
lean_dec_ref(v___x_1323_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1334_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1334_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1330_ = l_Array_append___redArg(v_a_1322_, v_a_1326_);
lean_dec(v_a_1326_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v___x_1330_);
v___x_1332_ = v___x_1328_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
lean_dec(v_a_1322_);
return v___x_1325_;
}
}
else
{
lean_dec_ref(v_arts_1315_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___boxed(lean_object* v_arts_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v_arts_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(lean_object* v_e_1338_){
_start:
{
if (lean_obj_tag(v_e_1338_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1349_; 
v_a_1340_ = lean_ctor_get(v_e_1338_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_e_1338_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1342_ = v_e_1338_;
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v_e_1338_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1349_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1347_; 
v___x_1344_ = lean_io_error_to_string(v_a_1340_);
v___x_1345_ = lean_mk_io_user_error(v___x_1344_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set_tag(v___x_1342_, 1);
lean_ctor_set(v___x_1342_, 0, v___x_1345_);
v___x_1347_ = v___x_1342_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_a_1350_ = lean_ctor_get(v_e_1338_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_e_1338_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v_e_1338_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v_e_1338_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 0);
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg___boxed(lean_object* v_e_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1358_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(lean_object* v_00_u03b1_1361_, lean_object* v_e_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v_e_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_e_1366_, lean_object* v_a_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0(v_00_u03b1_1365_, v_e_1366_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(lean_object* v_a_1369_, lean_object* v___y_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_fst_1373_; lean_object* v_snd_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1402_; 
v_fst_1373_ = lean_ctor_get(v_a_1371_, 0);
v_snd_1374_ = lean_ctor_get(v_a_1371_, 1);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_a_1371_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1376_ = v_a_1371_;
v_isShared_1377_ = v_isSharedCheck_1402_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_snd_1374_);
lean_inc(v_fst_1373_);
lean_dec(v_a_1371_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1402_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = lean_array_get_size(v_a_1369_);
v___x_1379_ = lean_nat_dec_lt(v_snd_1374_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1381_; 
if (v_isShared_1377_ == 0)
{
v___x_1381_ = v___x_1376_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_fst_1373_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_snd_1374_);
v___x_1381_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = l_Lean_instInhabitedModuleArtifacts_default;
v___x_1385_ = lean_array_get_borrowed(v___x_1384_, v_a_1369_, v_snd_1374_);
lean_inc(v___x_1385_);
v___x_1386_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions(v___x_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = l_Array_append___redArg(v_fst_1373_, v_a_1387_);
lean_dec(v_a_1387_);
v___x_1389_ = lean_nat_add(v_snd_1374_, v___y_1370_);
lean_dec(v_snd_1374_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v___x_1389_);
lean_ctor_set(v___x_1376_, 0, v___x_1388_);
v___x_1391_ = v___x_1376_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v_a_1371_ = v___x_1391_;
goto _start;
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_del_object(v___x_1376_);
lean_dec(v_snd_1374_);
lean_dec(v_fst_1373_);
v_a_1394_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1386_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1386_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg___boxed(lean_object* v_a_1403_, lean_object* v___y_1404_, lean_object* v_a_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1403_, v___y_1404_, v_a_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v_a_1403_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(lean_object* v_a_1408_, lean_object* v___y_1409_, lean_object* v___x_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1408_, v___y_1409_, v___x_1410_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1421_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1415_ = v___x_1412_;
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1412_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1421_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v_fst_1417_; lean_object* v___x_1419_; 
v_fst_1417_ = lean_ctor_get(v_a_1413_, 0);
lean_inc(v_fst_1417_);
lean_dec(v_a_1413_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 1);
lean_ctor_set(v___x_1415_, 0, v_fst_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_fst_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1412_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1412_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1412_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1412_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set_tag(v___x_1424_, 0);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed(lean_object* v_a_1430_, lean_object* v___y_1431_, lean_object* v___x_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0(v_a_1430_, v___y_1431_, v___x_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v_a_1430_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(lean_object* v_upperBound_1435_, lean_object* v_a_1436_, lean_object* v___y_1437_, lean_object* v_a_1438_, lean_object* v_b_1439_){
_start:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_lt(v_a_1438_, v_upperBound_1435_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; 
lean_dec(v_a_1438_);
lean_dec(v___y_1437_);
lean_dec_ref(v_a_1436_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_b_1439_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_readModuleArtifactRegions___closed__0));
lean_inc(v_a_1438_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v_a_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v_a_1436_);
v___f_1446_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1446_, 0, v_a_1436_);
lean_closure_set(v___f_1446_, 1, v___y_1437_);
lean_closure_set(v___f_1446_, 2, v___x_1445_);
v___x_1447_ = lean_io_as_task(v___f_1446_, v___x_1443_);
v___x_1448_ = lean_array_push(v_b_1439_, v___x_1447_);
v___x_1449_ = lean_unsigned_to_nat(1u);
v___x_1450_ = lean_nat_add(v_a_1438_, v___x_1449_);
lean_dec(v_a_1438_);
v_a_1438_ = v___x_1450_;
v_b_1439_ = v___x_1448_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg___boxed(lean_object* v_upperBound_1452_, lean_object* v_a_1453_, lean_object* v___y_1454_, lean_object* v_a_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1452_, v_a_1453_, v___y_1454_, v_a_1455_, v_b_1456_);
lean_dec(v_upperBound_1452_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(lean_object* v_as_1459_, size_t v_sz_1460_, size_t v_i_1461_, lean_object* v_b_1462_){
_start:
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_usize_dec_lt(v_i_1461_, v_sz_1460_);
if (v___x_1464_ == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_b_1462_);
return v___x_1465_;
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v_a_1466_ = lean_array_uget_borrowed(v_as_1459_, v_i_1461_);
lean_inc(v_a_1466_);
v___x_1467_ = lean_task_get_own(v_a_1466_);
v___x_1468_ = l_IO_ofExcept___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__0___redArg(v___x_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = l_Array_append___redArg(v_b_1462_, v_a_1469_);
lean_dec(v_a_1469_);
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_add(v_i_1461_, v___x_1471_);
v_i_1461_ = v___x_1472_;
v_b_1462_ = v___x_1470_;
goto _start;
}
else
{
lean_dec_ref(v_b_1462_);
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2___boxed(lean_object* v_as_1474_, lean_object* v_sz_1475_, lean_object* v_i_1476_, lean_object* v_b_1477_, lean_object* v___y_1478_){
_start:
{
size_t v_sz_boxed_1479_; size_t v_i_boxed_1480_; lean_object* v_res_1481_; 
v_sz_boxed_1479_ = lean_unbox_usize(v_sz_1475_);
lean_dec(v_sz_1475_);
v_i_boxed_1480_ = lean_unbox_usize(v_i_1476_);
lean_dec(v_i_1476_);
v_res_1481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_as_1474_, v_sz_boxed_1479_, v_i_boxed_1480_, v_b_1477_);
lean_dec_ref(v_as_1474_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(size_t v_sz_1482_, size_t v_i_1483_, lean_object* v_bs_1484_){
_start:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_usize_dec_lt(v_i_1483_, v_sz_1482_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1486_, 0, v_bs_1484_);
return v___x_1486_;
}
else
{
lean_object* v_v_1487_; lean_object* v___x_1488_; 
v_v_1487_ = lean_array_uget_borrowed(v_bs_1484_, v_i_1483_);
lean_inc(v_v_1487_);
v___x_1488_ = l_Lean_instFromJsonModuleArtifacts_fromJson(v_v_1487_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v_bs_1484_);
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1498_; lean_object* v_bs_x27_1499_; size_t v___x_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
v_a_1497_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1488_, 1);
v___x_1498_ = lean_unsigned_to_nat(0u);
v_bs_x27_1499_ = lean_array_uset(v_bs_1484_, v_i_1483_, v___x_1498_);
v___x_1500_ = ((size_t)1ULL);
v___x_1501_ = lean_usize_add(v_i_1483_, v___x_1500_);
v___x_1502_ = lean_array_uset(v_bs_x27_1499_, v_i_1483_, v_a_1497_);
v_i_1483_ = v___x_1501_;
v_bs_1484_ = v___x_1502_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1___boxed(lean_object* v_sz_1504_, lean_object* v_i_1505_, lean_object* v_bs_1506_){
_start:
{
size_t v_sz_boxed_1507_; size_t v_i_boxed_1508_; lean_object* v_res_1509_; 
v_sz_boxed_1507_ = lean_unbox_usize(v_sz_1504_);
lean_dec(v_sz_1504_);
v_i_boxed_1508_ = lean_unbox_usize(v_i_1505_);
lean_dec(v_i_1505_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_boxed_1507_, v_i_boxed_1508_, v_bs_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(lean_object* v_x_1512_){
_start:
{
if (lean_obj_tag(v_x_1512_) == 4)
{
lean_object* v_elems_1513_; size_t v_sz_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
v_elems_1513_ = lean_ctor_get(v_x_1512_, 0);
lean_inc_ref(v_elems_1513_);
lean_dec_ref_known(v_x_1512_, 1);
v_sz_1514_ = lean_array_size(v_elems_1513_);
v___x_1515_ = ((size_t)0ULL);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1_spec__1(v_sz_1514_, v___x_1515_, v_elems_1513_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1517_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__0));
v___x_1518_ = lean_unsigned_to_nat(80u);
v___x_1519_ = l_Lean_Json_pretty(v_x_1512_, v___x_1518_);
v___x_1520_ = lean_string_append(v___x_1517_, v___x_1519_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1___closed__1));
v___x_1522_ = lean_string_append(v___x_1520_, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
}
static uint32_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3(void){
_start:
{
lean_object* v___x_1527_; uint32_t v___x_1528_; 
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_internal_get_hardware_concurrency(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4(void){
_start:
{
uint32_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_uint32_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__3);
v___x_1530_ = lean_uint32_to_nat(v___x_1529_);
return v___x_1530_;
}
}
static uint8_t _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_unsigned_to_nat(4u);
v___x_1533_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1534_ = lean_nat_dec_le(v___x_1533_, v___x_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(lean_object* v_fname_1535_){
_start:
{
lean_object* v___x_1537_; lean_object* v_depsFile_1538_; lean_object* v___x_1539_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
lean_inc_ref(v_fname_1535_);
v_depsFile_1538_ = l_System_FilePath_addExtension(v_fname_1535_, v___x_1537_);
v___x_1539_ = l_IO_FS_readFile(v_depsFile_1538_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1626_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1626_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1626_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_a_1545_; lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Json_parse(v_a_1540_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; 
lean_dec_ref(v_fname_1535_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v_a_1545_ = v_a_1556_;
goto v___jp_1544_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1558_; 
v_a_1557_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1557_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1558_ = l_Lean_Array_fromJson_x3f___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__1(v_a_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; 
lean_dec_ref(v_fname_1535_);
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v_a_1545_ = v_a_1559_;
goto v___jp_1544_;
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___y_1564_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1615_; uint8_t v___x_1625_; 
lean_del_object(v___x_1542_);
lean_dec_ref(v_depsFile_1538_);
v_a_1560_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1561_ = lean_obj_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__4);
v___x_1562_ = lean_unsigned_to_nat(4u);
v___x_1625_ = lean_uint8_once(&l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6, &l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6_once, _init_l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__6);
if (v___x_1625_ == 0)
{
v___y_1615_ = v___x_1562_;
goto v___jp_1614_;
}
else
{
v___y_1615_ = v___x_1561_;
goto v___jp_1614_;
}
v___jp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_mk_empty_array_with_capacity(v___y_1564_);
v___x_1566_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_1560_);
lean_inc(v___y_1564_);
v___x_1567_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v___y_1564_, v_a_1560_, v___y_1564_, v___x_1566_, v___x_1565_);
lean_dec(v___y_1564_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; size_t v_sz_1572_; size_t v___x_1573_; lean_object* v___x_1574_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = lean_array_get_size(v_a_1560_);
lean_dec(v_a_1560_);
v___x_1570_ = lean_nat_mul(v___x_1569_, v___x_1562_);
v___x_1571_ = lean_mk_empty_array_with_capacity(v___x_1570_);
lean_dec(v___x_1570_);
v_sz_1572_ = lean_array_size(v_a_1568_);
v___x_1573_ = ((size_t)0ULL);
v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__2(v_a_1568_, v_sz_1572_, v___x_1573_, v___x_1571_);
lean_dec(v_a_1568_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = lean_compacted_region_read(v_fname_1535_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_fname_1535_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_fst_1581_; lean_object* v___x_1583_; 
v_fst_1581_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_fst_1581_);
lean_dec(v_a_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_fst_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_fst_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1586_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1576_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1576_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_fname_1535_);
v_a_1594_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1574_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1574_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_a_1560_);
lean_dec_ref(v_fname_1535_);
v_a_1602_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1567_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1567_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
v___jp_1610_:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_nat_dec_le(v___y_1611_, v___y_1612_);
if (v___x_1613_ == 0)
{
lean_dec(v___y_1612_);
v___y_1564_ = v___y_1611_;
goto v___jp_1563_;
}
else
{
lean_dec(v___y_1611_);
v___y_1564_ = v___y_1612_;
goto v___jp_1563_;
}
}
v___jp_1614_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__5));
v___x_1617_ = lean_io_getenv(v___x_1616_);
v___x_1618_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v___x_1617_) == 0)
{
v___y_1611_ = v___x_1618_;
v___y_1612_ = v___y_1615_;
goto v___jp_1610_;
}
else
{
lean_object* v_val_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_val_1619_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_string_utf8_byte_size(v_val_1619_);
v___x_1622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1622_, 0, v_val_1619_);
lean_ctor_set(v___x_1622_, 1, v___x_1620_);
lean_ctor_set(v___x_1622_, 2, v___x_1621_);
v___x_1623_ = l_String_Slice_toNat_x3f(v___x_1622_);
lean_dec_ref_known(v___x_1622_, 3);
if (lean_obj_tag(v___x_1623_) == 0)
{
v___y_1611_ = v___x_1618_;
v___y_1612_ = v___y_1615_;
goto v___jp_1610_;
}
else
{
lean_object* v_val_1624_; 
lean_dec(v___y_1615_);
v_val_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v___y_1611_ = v___x_1618_;
v___y_1612_ = v_val_1624_;
goto v___jp_1610_;
}
}
}
}
}
v___jp_1544_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__1));
v___x_1547_ = lean_string_append(v___x_1546_, v_depsFile_1538_);
lean_dec_ref(v_depsFile_1538_);
v___x_1548_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__2));
v___x_1549_ = lean_string_append(v___x_1547_, v___x_1548_);
v___x_1550_ = lean_string_append(v___x_1549_, v_a_1545_);
lean_dec_ref(v_a_1545_);
v___x_1551_ = lean_mk_io_user_error(v___x_1550_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 1);
lean_ctor_set(v___x_1542_, 0, v___x_1551_);
v___x_1553_ = v___x_1542_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_depsFile_1538_);
lean_dec_ref(v_fname_1535_);
v_a_1627_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1539_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1539_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___boxed(lean_object* v_fname_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_fname_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(lean_object* v_a_1638_, lean_object* v___y_1639_, lean_object* v_inst_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___redArg(v_a_1638_, v___y_1639_, v_a_1641_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3___boxed(lean_object* v_a_1644_, lean_object* v___y_1645_, lean_object* v_inst_1646_, lean_object* v_a_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__3(v_a_1644_, v___y_1645_, v_inst_1646_, v_a_1647_);
lean_dec(v___y_1645_);
lean_dec_ref(v_a_1644_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(lean_object* v_upperBound_1650_, lean_object* v_a_1651_, lean_object* v___y_1652_, lean_object* v_inst_1653_, lean_object* v_R_1654_, lean_object* v_a_1655_, lean_object* v_b_1656_, lean_object* v_c_1657_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___redArg(v_upperBound_1650_, v_a_1651_, v___y_1652_, v_a_1655_, v_b_1656_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4___boxed(lean_object* v_upperBound_1660_, lean_object* v_a_1661_, lean_object* v___y_1662_, lean_object* v_inst_1663_, lean_object* v_R_1664_, lean_object* v_a_1665_, lean_object* v_b_1666_, lean_object* v_c_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot_spec__4(v_upperBound_1660_, v_a_1661_, v___y_1662_, v_inst_1663_, v_R_1664_, v_a_1665_, v_b_1666_, v_c_1667_);
lean_dec(v_upperBound_1660_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(lean_object* v_as_1670_, size_t v_sz_1671_, size_t v_i_1672_, lean_object* v_b_1673_){
_start:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_lt(v_i_1672_, v_sz_1671_);
if (v___x_1675_ == 0)
{
return v_b_1673_;
}
else
{
lean_object* v_a_1676_; lean_object* v_cancelTk_x3f_1677_; lean_object* v___x_1678_; 
v_a_1676_ = lean_array_uget_borrowed(v_as_1670_, v_i_1672_);
v_cancelTk_x3f_1677_ = lean_ctor_get(v_a_1676_, 2);
v___x_1678_ = lean_box(0);
if (lean_obj_tag(v_cancelTk_x3f_1677_) == 1)
{
lean_object* v_val_1685_; lean_object* v___x_1686_; 
v_val_1685_ = lean_ctor_get(v_cancelTk_x3f_1677_, 0);
v___x_1686_ = l_IO_CancelToken_set(v_val_1685_);
goto v___jp_1679_;
}
else
{
goto v___jp_1679_;
}
v___jp_1679_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; 
lean_inc(v_a_1676_);
v___x_1680_ = l_Lean_Language_SnapshotTask_get___redArg(v_a_1676_);
v___x_1681_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___x_1680_);
lean_dec(v___x_1680_);
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1672_, v___x_1682_);
v_i_1672_ = v___x_1683_;
v_b_1673_ = v___x_1678_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(lean_object* v_s_1687_){
_start:
{
lean_object* v_children_1689_; lean_object* v___x_1690_; size_t v_sz_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v_children_1689_ = lean_ctor_get(v_s_1687_, 1);
v___x_1690_ = lean_box(0);
v_sz_1691_ = lean_array_size(v_children_1689_);
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_children_1689_, v_sz_1691_, v___x_1692_, v___x_1690_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave___boxed(lean_object* v_s_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v_s_1694_);
lean_dec_ref(v_s_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0___boxed(lean_object* v_as_1697_, lean_object* v_sz_1698_, lean_object* v_i_1699_, lean_object* v_b_1700_, lean_object* v___y_1701_){
_start:
{
size_t v_sz_boxed_1702_; size_t v_i_boxed_1703_; lean_object* v_res_1704_; 
v_sz_boxed_1702_ = lean_unbox_usize(v_sz_1698_);
lean_dec(v_sz_1698_);
v_i_boxed_1703_ = lean_unbox_usize(v_i_1699_);
lean_dec(v_i_1699_);
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave_spec__0(v_as_1697_, v_sz_boxed_1702_, v_i_boxed_1703_, v_b_1700_);
lean_dec_ref(v_as_1697_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(lean_object* v_snap_1705_, lean_object* v_m_1706_){
_start:
{
lean_object* v_result_x3f_1707_; 
v_result_x3f_1707_ = lean_ctor_get(v_snap_1705_, 4);
lean_inc(v_result_x3f_1707_);
if (lean_obj_tag(v_result_x3f_1707_) == 1)
{
lean_object* v_val_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1808_; 
v_val_1708_ = lean_ctor_get(v_result_x3f_1707_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_result_x3f_1707_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1710_ = v_result_x3f_1707_;
v_isShared_1711_ = v_isSharedCheck_1808_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_val_1708_);
lean_dec(v_result_x3f_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1808_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_toSnapshot_1712_; lean_object* v_metaSnap_1713_; lean_object* v_ictx_1714_; lean_object* v_stx_1715_; lean_object* v_parserState_1716_; lean_object* v_processedSnap_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1807_; 
v_toSnapshot_1712_ = lean_ctor_get(v_snap_1705_, 0);
v_metaSnap_1713_ = lean_ctor_get(v_snap_1705_, 1);
v_ictx_1714_ = lean_ctor_get(v_snap_1705_, 2);
v_stx_1715_ = lean_ctor_get(v_snap_1705_, 3);
v_parserState_1716_ = lean_ctor_get(v_val_1708_, 0);
v_processedSnap_1717_ = lean_ctor_get(v_val_1708_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_val_1708_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1719_ = v_val_1708_;
v_isShared_1720_ = v_isSharedCheck_1807_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_processedSnap_1717_);
lean_inc(v_parserState_1716_);
lean_dec(v_val_1708_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1807_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_processed_1721_; lean_object* v_result_x3f_1722_; 
v_processed_1721_ = l_Lean_Language_SnapshotTask_get___redArg(v_processedSnap_1717_);
v_result_x3f_1722_ = lean_ctor_get(v_processed_1721_, 2);
lean_inc(v_result_x3f_1722_);
if (lean_obj_tag(v_result_x3f_1722_) == 1)
{
lean_object* v_val_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1806_; 
v_val_1723_ = lean_ctor_get(v_result_x3f_1722_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_result_x3f_1722_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1725_ = v_result_x3f_1722_;
v_isShared_1726_ = v_isSharedCheck_1806_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_val_1723_);
lean_dec(v_result_x3f_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1806_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v_cmdState_1727_; lean_object* v_toSnapshot_1728_; lean_object* v_metaSnap_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1804_; 
v_cmdState_1727_ = lean_ctor_get(v_val_1723_, 0);
lean_inc_ref(v_cmdState_1727_);
v_toSnapshot_1728_ = lean_ctor_get(v_processed_1721_, 0);
v_metaSnap_1729_ = lean_ctor_get(v_processed_1721_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_processed_1721_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v_processed_1721_, 2);
lean_dec(v_unused_1805_);
v___x_1731_ = v_processed_1721_;
v_isShared_1732_ = v_isSharedCheck_1804_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_metaSnap_1729_);
lean_inc(v_toSnapshot_1728_);
lean_dec(v_processed_1721_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1804_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_firstCmdSnap_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1802_; 
v_firstCmdSnap_1733_ = lean_ctor_get(v_val_1723_, 1);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_val_1723_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; 
v_unused_1803_ = lean_ctor_get(v_val_1723_, 0);
lean_dec(v_unused_1803_);
v___x_1735_ = v_val_1723_;
v_isShared_1736_ = v_isSharedCheck_1802_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_firstCmdSnap_1733_);
lean_dec(v_val_1723_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1802_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v_env_1737_; lean_object* v_messages_1738_; lean_object* v_scopes_1739_; lean_object* v_usedQuotCtxts_1740_; lean_object* v_nextMacroScope_1741_; lean_object* v_maxRecDepth_1742_; lean_object* v_ngen_1743_; lean_object* v_auxDeclNGen_1744_; lean_object* v_infoState_1745_; lean_object* v_traceState_1746_; lean_object* v_snapshotTasks_1747_; lean_object* v_prevLinterStates_1748_; lean_object* v_codeQualityEntryTasks_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1801_; 
v_env_1737_ = lean_ctor_get(v_cmdState_1727_, 0);
v_messages_1738_ = lean_ctor_get(v_cmdState_1727_, 1);
v_scopes_1739_ = lean_ctor_get(v_cmdState_1727_, 2);
v_usedQuotCtxts_1740_ = lean_ctor_get(v_cmdState_1727_, 3);
v_nextMacroScope_1741_ = lean_ctor_get(v_cmdState_1727_, 4);
v_maxRecDepth_1742_ = lean_ctor_get(v_cmdState_1727_, 5);
v_ngen_1743_ = lean_ctor_get(v_cmdState_1727_, 6);
v_auxDeclNGen_1744_ = lean_ctor_get(v_cmdState_1727_, 7);
v_infoState_1745_ = lean_ctor_get(v_cmdState_1727_, 8);
v_traceState_1746_ = lean_ctor_get(v_cmdState_1727_, 9);
v_snapshotTasks_1747_ = lean_ctor_get(v_cmdState_1727_, 10);
v_prevLinterStates_1748_ = lean_ctor_get(v_cmdState_1727_, 11);
v_codeQualityEntryTasks_1749_ = lean_ctor_get(v_cmdState_1727_, 12);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_cmdState_1727_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1751_ = v_cmdState_1727_;
v_isShared_1752_ = v_isSharedCheck_1801_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1749_);
lean_inc(v_prevLinterStates_1748_);
lean_inc(v_snapshotTasks_1747_);
lean_inc(v_traceState_1746_);
lean_inc(v_infoState_1745_);
lean_inc(v_auxDeclNGen_1744_);
lean_inc(v_ngen_1743_);
lean_inc(v_maxRecDepth_1742_);
lean_inc(v_nextMacroScope_1741_);
lean_inc(v_usedQuotCtxts_1740_);
lean_inc(v_scopes_1739_);
lean_inc(v_messages_1738_);
lean_inc(v_env_1737_);
lean_dec(v_cmdState_1727_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1801_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v_mainModule_1754_; uint8_t v___x_1755_; 
v___x_1753_ = l_Lean_Environment_header(v_env_1737_);
v_mainModule_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_mainModule_1754_);
lean_dec_ref(v___x_1753_);
v___x_1755_ = lean_name_eq(v_mainModule_1754_, v_m_1706_);
lean_dec(v_mainModule_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1795_; 
lean_inc(v_stx_1715_);
lean_inc_ref(v_ictx_1714_);
lean_inc_ref(v_metaSnap_1713_);
lean_inc_ref(v_toSnapshot_1712_);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_snap_1705_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; lean_object* v_unused_1797_; lean_object* v_unused_1798_; lean_object* v_unused_1799_; lean_object* v_unused_1800_; 
v_unused_1796_ = lean_ctor_get(v_snap_1705_, 4);
lean_dec(v_unused_1796_);
v_unused_1797_ = lean_ctor_get(v_snap_1705_, 3);
lean_dec(v_unused_1797_);
v_unused_1798_ = lean_ctor_get(v_snap_1705_, 2);
lean_dec(v_unused_1798_);
v_unused_1799_ = lean_ctor_get(v_snap_1705_, 1);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v_snap_1705_, 0);
lean_dec(v_unused_1800_);
v___x_1757_ = v_snap_1705_;
v_isShared_1758_ = v_isSharedCheck_1795_;
goto v_resetjp_1756_;
}
else
{
lean_dec(v_snap_1705_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1795_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v_idx_1759_; lean_object* v_parentIdxs_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1793_; 
v_idx_1759_ = lean_ctor_get(v_auxDeclNGen_1744_, 1);
v_parentIdxs_1760_ = lean_ctor_get(v_auxDeclNGen_1744_, 2);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_auxDeclNGen_1744_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v_auxDeclNGen_1744_, 0);
lean_dec(v_unused_1794_);
v___x_1762_ = v_auxDeclNGen_1744_;
v_isShared_1763_ = v_isSharedCheck_1793_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_parentIdxs_1760_);
lean_inc(v_idx_1759_);
lean_dec(v_auxDeclNGen_1744_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1793_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v_newEnv_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1768_; 
v_newEnv_1764_ = l_Lean_Environment_setMainModule(v_env_1737_, v_m_1706_);
v___x_1765_ = lean_box(0);
v___x_1766_ = l_Lean_mkPrivateName(v_newEnv_1764_, v___x_1765_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1766_);
v___x_1768_ = v___x_1762_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_idx_1759_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_parentIdxs_1760_);
v___x_1768_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v_newCmdState_1770_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 7, v___x_1768_);
lean_ctor_set(v___x_1751_, 0, v_newEnv_1764_);
v_newCmdState_1770_ = v___x_1751_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_newEnv_1764_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_messages_1738_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_scopes_1739_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_usedQuotCtxts_1740_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_nextMacroScope_1741_);
lean_ctor_set(v_reuseFailAlloc_1791_, 5, v_maxRecDepth_1742_);
lean_ctor_set(v_reuseFailAlloc_1791_, 6, v_ngen_1743_);
lean_ctor_set(v_reuseFailAlloc_1791_, 7, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1791_, 8, v_infoState_1745_);
lean_ctor_set(v_reuseFailAlloc_1791_, 9, v_traceState_1746_);
lean_ctor_set(v_reuseFailAlloc_1791_, 10, v_snapshotTasks_1747_);
lean_ctor_set(v_reuseFailAlloc_1791_, 11, v_prevLinterStates_1748_);
lean_ctor_set(v_reuseFailAlloc_1791_, 12, v_codeQualityEntryTasks_1749_);
v_newCmdState_1770_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v_newCmdState_1770_);
v___x_1772_ = v___x_1735_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_newCmdState_1770_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_firstCmdSnap_1733_);
v___x_1772_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1772_);
v___x_1774_ = v___x_1725_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v_newProcessed_1776_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 2, v___x_1774_);
v_newProcessed_1776_ = v___x_1731_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_toSnapshot_1728_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_metaSnap_1729_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v___x_1774_);
v_newProcessed_1776_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = l_Lean_Language_SnapshotTask_finished___redArg(v___x_1777_, v_newProcessed_1776_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1778_);
v___x_1780_ = v___x_1719_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_parserState_1716_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1780_);
v___x_1782_ = v___x_1710_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 4, v___x_1782_);
v___x_1784_ = v___x_1757_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_toSnapshot_1712_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_metaSnap_1713_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_ictx_1714_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_stx_1715_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
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
lean_del_object(v___x_1751_);
lean_dec_ref(v_codeQualityEntryTasks_1749_);
lean_dec(v_prevLinterStates_1748_);
lean_dec_ref(v_snapshotTasks_1747_);
lean_dec_ref(v_traceState_1746_);
lean_dec_ref(v_infoState_1745_);
lean_dec_ref(v_auxDeclNGen_1744_);
lean_dec_ref(v_ngen_1743_);
lean_dec(v_maxRecDepth_1742_);
lean_dec(v_nextMacroScope_1741_);
lean_dec(v_usedQuotCtxts_1740_);
lean_dec(v_scopes_1739_);
lean_dec_ref(v_messages_1738_);
lean_dec_ref(v_env_1737_);
lean_del_object(v___x_1735_);
lean_dec_ref(v_firstCmdSnap_1733_);
lean_del_object(v___x_1731_);
lean_dec_ref(v_metaSnap_1729_);
lean_dec_ref(v_toSnapshot_1728_);
lean_del_object(v___x_1725_);
lean_del_object(v___x_1719_);
lean_dec_ref(v_parserState_1716_);
lean_del_object(v___x_1710_);
lean_dec(v_m_1706_);
return v_snap_1705_;
}
}
}
}
}
}
else
{
lean_dec(v_result_x3f_1722_);
lean_dec(v_processed_1721_);
lean_del_object(v___x_1719_);
lean_dec_ref(v_parserState_1716_);
lean_del_object(v___x_1710_);
lean_dec(v_m_1706_);
return v_snap_1705_;
}
}
}
}
else
{
lean_dec(v_result_x3f_1707_);
lean_dec(v_m_1706_);
return v_snap_1705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(lean_object* v_incrFile_1809_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_incrFile_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1___boxed(lean_object* v_incrFile_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__1(v_incrFile_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(lean_object* v_opts_1815_, lean_object* v_incr_1816_, lean_object* v_res_1817_){
_start:
{
lean_object* v_cmdState_1819_; lean_object* v_env_1820_; lean_object* v_initModIdxs_1821_; lean_object* v___x_1822_; 
v_cmdState_1819_ = lean_ctor_get(v_res_1817_, 0);
lean_inc_ref(v_cmdState_1819_);
lean_dec_ref(v_res_1817_);
v_env_1820_ = lean_ctor_get(v_cmdState_1819_, 0);
lean_inc_ref(v_env_1820_);
lean_dec_ref(v_cmdState_1819_);
v_initModIdxs_1821_ = lean_ctor_get(v_incr_1816_, 1);
v___x_1822_ = l_Lean_runInitAttrsForModules(v_env_1820_, v_initModIdxs_1821_, v_opts_1815_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4___boxed(lean_object* v_opts_1823_, lean_object* v_incr_1824_, lean_object* v_res_1825_, lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__4(v_opts_1823_, v_incr_1824_, v_res_1825_);
lean_dec_ref(v_incr_1824_);
lean_dec_ref(v_opts_1823_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7(){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_enable_initializer_execution();
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7___boxed(lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__7();
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(lean_object* v_env_1835_, lean_object* v_incrFile_1836_, lean_object* v_toSave_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v_regions_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1839_ = l_Lean_Environment_header(v_env_1835_);
v_regions_1840_ = lean_ctor_get(v___x_1839_, 2);
lean_inc_ref(v_regions_1840_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1842_ = lean_box(0);
v___x_1843_ = 1;
v___x_1844_ = lean_compacted_region_save(v_incrFile_1836_, v___x_1841_, v_toSave_1837_, v_regions_1840_, v___x_1842_, v___x_1843_);
lean_dec_ref(v_regions_1840_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___boxed(lean_object* v_env_1845_, lean_object* v_incrFile_1846_, lean_object* v_toSave_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12(v_env_1845_, v_incrFile_1846_, v_toSave_1847_);
lean_dec_ref(v_toSave_1847_);
lean_dec_ref(v_incrFile_1846_);
lean_dec_ref(v_env_1845_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__5(lean_object* v_opts_1850_, lean_object* v_opt_1851_){
_start:
{
lean_object* v_name_1852_; lean_object* v_map_1853_; lean_object* v___x_1854_; 
v_name_1852_ = lean_ctor_get(v_opt_1851_, 0);
v_map_1853_ = lean_ctor_get(v_opts_1850_, 0);
v___x_1854_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1853_, v_name_1852_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_box(0);
return v___x_1855_;
}
else
{
lean_object* v_val_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1865_; 
v_val_1856_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1858_ = v___x_1854_;
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_val_1856_);
lean_dec(v___x_1854_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1865_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
if (lean_obj_tag(v_val_1856_) == 0)
{
lean_object* v_v_1860_; lean_object* v___x_1862_; 
v_v_1860_ = lean_ctor_get(v_val_1856_, 0);
lean_inc_ref(v_v_1860_);
lean_dec_ref_known(v_val_1856_, 1);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v_v_1860_);
v___x_1862_ = v___x_1858_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_v_1860_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
else
{
lean_object* v___x_1864_; 
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
v___x_1864_ = lean_box(0);
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__5___boxed(lean_object* v_opts_1866_, lean_object* v_opt_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__5(v_opts_1866_, v_opt_1867_);
lean_dec_ref(v_opt_1867_);
lean_dec_ref(v_opts_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__7(lean_object* v_opts_1869_, lean_object* v_opt_1870_){
_start:
{
lean_object* v_name_1871_; lean_object* v_defValue_1872_; lean_object* v_map_1873_; lean_object* v___x_1874_; 
v_name_1871_ = lean_ctor_get(v_opt_1870_, 0);
v_defValue_1872_ = lean_ctor_get(v_opt_1870_, 1);
v_map_1873_ = lean_ctor_get(v_opts_1869_, 0);
v___x_1874_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1873_, v_name_1871_);
if (lean_obj_tag(v___x_1874_) == 0)
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_unbox(v_defValue_1872_);
return v___x_1875_;
}
else
{
lean_object* v_val_1876_; 
v_val_1876_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_val_1876_);
lean_dec_ref_known(v___x_1874_, 1);
if (lean_obj_tag(v_val_1876_) == 1)
{
uint8_t v_v_1877_; 
v_v_1877_ = lean_ctor_get_uint8(v_val_1876_, 0);
lean_dec_ref_known(v_val_1876_, 0);
return v_v_1877_;
}
else
{
uint8_t v___x_1878_; 
lean_dec(v_val_1876_);
v___x_1878_ = lean_unbox(v_defValue_1872_);
return v___x_1878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__7___boxed(lean_object* v_opts_1879_, lean_object* v_opt_1880_){
_start:
{
uint8_t v_res_1881_; lean_object* v_r_1882_; 
v_res_1881_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__7(v_opts_1879_, v_opt_1880_);
lean_dec_ref(v_opt_1880_);
lean_dec_ref(v_opts_1879_);
v_r_1882_ = lean_box(v_res_1881_);
return v_r_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0(lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_hOpt_1885_){
_start:
{
lean_inc_ref(v_hOpt_1885_);
return v_hOpt_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__0___boxed(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_hOpt_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_Elab_runFrontend___lam__0(v_x_1886_, v_x_1887_, v_hOpt_1888_);
lean_dec_ref(v_hOpt_1888_);
lean_dec_ref(v_x_1887_);
lean_dec(v_x_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4_spec__7(size_t v_sz_1890_, size_t v_i_1891_, lean_object* v_bs_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_usize_dec_lt(v_i_1891_, v_sz_1890_);
if (v___x_1893_ == 0)
{
return v_bs_1892_;
}
else
{
lean_object* v_v_1894_; lean_object* v___x_1895_; lean_object* v_bs_x27_1896_; lean_object* v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v_v_1894_ = lean_array_uget(v_bs_1892_, v_i_1891_);
v___x_1895_ = lean_unsigned_to_nat(0u);
v_bs_x27_1896_ = lean_array_uset(v_bs_1892_, v_i_1891_, v___x_1895_);
v___x_1897_ = l_Lean_instToJsonModuleArtifacts_toJson(v_v_1894_);
v___x_1898_ = ((size_t)1ULL);
v___x_1899_ = lean_usize_add(v_i_1891_, v___x_1898_);
v___x_1900_ = lean_array_uset(v_bs_x27_1896_, v_i_1891_, v___x_1897_);
v_i_1891_ = v___x_1899_;
v_bs_1892_ = v___x_1900_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4_spec__7___boxed(lean_object* v_sz_1902_, lean_object* v_i_1903_, lean_object* v_bs_1904_){
_start:
{
size_t v_sz_boxed_1905_; size_t v_i_boxed_1906_; lean_object* v_res_1907_; 
v_sz_boxed_1905_ = lean_unbox_usize(v_sz_1902_);
lean_dec(v_sz_1902_);
v_i_boxed_1906_ = lean_unbox_usize(v_i_1903_);
lean_dec(v_i_1903_);
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4_spec__7(v_sz_boxed_1905_, v_i_boxed_1906_, v_bs_1904_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4(lean_object* v_a_1908_){
_start:
{
size_t v_sz_1909_; size_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_sz_1909_ = lean_array_size(v_a_1908_);
v___x_1910_ = ((size_t)0ULL);
v___x_1911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4_spec__7(v_sz_1909_, v___x_1910_, v_a_1908_);
v___x_1912_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1(lean_object* v_a_1913_, uint8_t v___x_1914_, lean_object* v_incrFile_1915_, lean_object* v_snapToSave_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v_regions_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1918_ = l_Lean_Environment_header(v_a_1913_);
v_regions_1919_ = lean_ctor_get(v___x_1918_, 2);
lean_inc_ref(v_regions_1919_);
lean_dec_ref(v___x_1918_);
v___x_1920_ = l_Lean_getRegularInitAttrModIdxs(v_a_1913_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_snapToSave_1916_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_runFrontend_unsafe__12___closed__1));
v___x_1923_ = lean_box(0);
v___x_1924_ = lean_compacted_region_save(v_incrFile_1915_, v___x_1922_, v___x_1921_, v_regions_1919_, v___x_1923_, v___x_1914_);
lean_dec_ref_known(v___x_1921_, 2);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
v___x_1926_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_regionsToModuleArtifacts(v_regions_1919_);
lean_dec_ref(v_regions_1919_);
v___x_1927_ = ((lean_object*)(l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot___closed__0));
v___x_1928_ = l_System_FilePath_addExtension(v_incrFile_1915_, v___x_1927_);
v___x_1929_ = l_Lean_Array_toJson___at___00Lean_Elab_runFrontend_spec__4(v___x_1926_);
v___x_1930_ = l_Lean_Json_compress(v___x_1929_);
v___x_1931_ = l_IO_FS_writeFile(v___x_1928_, v___x_1930_);
lean_dec_ref(v___x_1930_);
lean_dec_ref(v___x_1928_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1939_; 
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1931_, 0);
lean_dec(v_unused_1940_);
v___x_1933_ = v___x_1931_;
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
else
{
lean_dec(v___x_1931_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1939_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = lean_runtime_forget(v_a_1925_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1935_);
v___x_1937_ = v___x_1933_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_dec(v_a_1925_);
return v___x_1931_;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_regions_1919_);
lean_dec_ref(v_incrFile_1915_);
v_a_1941_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1924_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1924_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__1___boxed(lean_object* v_a_1949_, lean_object* v___x_1950_, lean_object* v_incrFile_1951_, lean_object* v_snapToSave_1952_, lean_object* v___y_1953_){
_start:
{
uint8_t v___x_5788__boxed_1954_; lean_object* v_res_1955_; 
v___x_5788__boxed_1954_ = lean_unbox(v___x_1950_);
v_res_1955_ = l_Lean_Elab_runFrontend___lam__1(v_a_1949_, v___x_5788__boxed_1954_, v_incrFile_1951_, v_snapToSave_1952_);
lean_dec_ref(v_a_1949_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2(lean_object* v_fileMap_1956_, lean_object* v_a_1957_, lean_object* v___x_1958_, lean_object* v_opts_1959_, lean_object* v_val_1960_, uint8_t v___x_1961_, uint8_t v_a_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1964_ = l_Lean_Linter_recordLints(v_fileMap_1956_, v_a_1957_, v___x_1958_);
v___x_1965_ = l_Lean_Compiler_compiler_postponeCompile;
v___x_1966_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__7(v_opts_1959_, v___x_1965_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_writeModule(v___x_1964_, v_val_1960_, v___x_1961_);
return v___x_1967_;
}
else
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_writeModule(v___x_1964_, v_val_1960_, v_a_1962_);
return v___x_1968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__2___boxed(lean_object* v_fileMap_1969_, lean_object* v_a_1970_, lean_object* v___x_1971_, lean_object* v_opts_1972_, lean_object* v_val_1973_, lean_object* v___x_1974_, lean_object* v_a_1975_, lean_object* v___y_1976_){
_start:
{
uint8_t v___x_5862__boxed_1977_; uint8_t v_a_5863__boxed_1978_; lean_object* v_res_1979_; 
v___x_5862__boxed_1977_ = lean_unbox(v___x_1974_);
v_a_5863__boxed_1978_ = lean_unbox(v_a_1975_);
v_res_1979_ = l_Lean_Elab_runFrontend___lam__2(v_fileMap_1969_, v_a_1970_, v___x_1971_, v_opts_1972_, v_val_1973_, v___x_5862__boxed_1977_, v_a_5863__boxed_1978_);
lean_dec_ref(v_opts_1972_);
lean_dec_ref(v___x_1971_);
lean_dec_ref(v_fileMap_1969_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(lean_object* v_as_1980_, size_t v_i_1981_, size_t v_stop_1982_, lean_object* v_b_1983_){
_start:
{
uint8_t v___x_1985_; 
v___x_1985_ = lean_usize_dec_eq(v_i_1981_, v_stop_1982_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_array_uget_borrowed(v_as_1980_, v_i_1981_);
lean_inc(v___x_1986_);
v___x_1987_ = lean_load_dynlib(v___x_1986_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; size_t v___x_1989_; size_t v___x_1990_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1981_, v___x_1989_);
v_i_1981_ = v___x_1990_;
v_b_1983_ = v_a_1988_;
goto _start;
}
else
{
return v___x_1987_;
}
}
else
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_b_1983_);
return v___x_1992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1___boxed(lean_object* v_as_1993_, lean_object* v_i_1994_, lean_object* v_stop_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_){
_start:
{
size_t v_i_boxed_1998_; size_t v_stop_boxed_1999_; lean_object* v_res_2000_; 
v_i_boxed_1998_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_stop_boxed_1999_ = lean_unbox_usize(v_stop_1995_);
lean_dec(v_stop_1995_);
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_as_1993_, v_i_boxed_1998_, v_stop_boxed_1999_, v_b_1996_);
lean_dec_ref(v_as_1993_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3(lean_object* v_setup_x3f_2001_, lean_object* v___f_2002_, lean_object* v___x_2003_, lean_object* v_plugins_2004_, uint32_t v_trustLevel_2005_, uint8_t v___x_2006_, lean_object* v_mainModuleName_2007_, lean_object* v_stx_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; uint8_t v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; 
if (lean_obj_tag(v_setup_x3f_2001_) == 1)
{
lean_object* v_val_2025_; lean_object* v_name_2026_; lean_object* v_package_x3f_2027_; uint8_t v_isModule_2028_; lean_object* v_imports_x3f_2029_; lean_object* v_importArts_2030_; lean_object* v_dynlibs_2031_; lean_object* v_plugins_2032_; lean_object* v_options_2033_; lean_object* v___y_2040_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
lean_dec(v_mainModuleName_2007_);
v_val_2025_ = lean_ctor_get(v_setup_x3f_2001_, 0);
lean_inc(v_val_2025_);
lean_dec_ref_known(v_setup_x3f_2001_, 1);
v_name_2026_ = lean_ctor_get(v_val_2025_, 0);
lean_inc(v_name_2026_);
v_package_x3f_2027_ = lean_ctor_get(v_val_2025_, 1);
lean_inc(v_package_x3f_2027_);
v_isModule_2028_ = lean_ctor_get_uint8(v_val_2025_, sizeof(void*)*7);
v_imports_x3f_2029_ = lean_ctor_get(v_val_2025_, 2);
lean_inc(v_imports_x3f_2029_);
v_importArts_2030_ = lean_ctor_get(v_val_2025_, 3);
lean_inc(v_importArts_2030_);
v_dynlibs_2031_ = lean_ctor_get(v_val_2025_, 4);
lean_inc_ref(v_dynlibs_2031_);
v_plugins_2032_ = lean_ctor_get(v_val_2025_, 5);
lean_inc_ref(v_plugins_2032_);
v_options_2033_ = lean_ctor_get(v_val_2025_, 6);
lean_inc(v_options_2033_);
lean_dec(v_val_2025_);
v___x_2049_ = lean_unsigned_to_nat(0u);
v___x_2050_ = lean_array_get_size(v_dynlibs_2031_);
v___x_2051_ = lean_nat_dec_lt(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_dec_ref(v_dynlibs_2031_);
goto v___jp_2034_;
}
else
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_nat_dec_le(v___x_2050_, v___x_2050_);
if (v___x_2053_ == 0)
{
if (v___x_2051_ == 0)
{
lean_dec_ref(v_dynlibs_2031_);
goto v___jp_2034_;
}
else
{
size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = lean_usize_of_nat(v___x_2050_);
v___x_2056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2031_, v___x_2054_, v___x_2055_, v___x_2052_);
lean_dec_ref(v_dynlibs_2031_);
v___y_2040_ = v___x_2056_;
goto v___jp_2039_;
}
}
else
{
size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = lean_usize_of_nat(v___x_2050_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__1(v_dynlibs_2031_, v___x_2057_, v___x_2058_, v___x_2052_);
lean_dec_ref(v_dynlibs_2031_);
v___y_2040_ = v___x_2059_;
goto v___jp_2039_;
}
}
v___jp_2034_:
{
uint8_t v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2008_);
v___x_2036_ = lean_strict_or(v_isModule_2028_, v___x_2035_);
if (lean_obj_tag(v_imports_x3f_2029_) == 0)
{
lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2008_, v___x_2006_);
v___y_2012_ = v_plugins_2032_;
v___y_2013_ = v_options_2033_;
v___y_2014_ = v_name_2026_;
v___y_2015_ = v_importArts_2030_;
v___y_2016_ = v___x_2036_;
v___y_2017_ = v_package_x3f_2027_;
v___y_2018_ = v___x_2037_;
goto v___jp_2011_;
}
else
{
lean_object* v_val_2038_; 
lean_dec(v_stx_2008_);
v_val_2038_ = lean_ctor_get(v_imports_x3f_2029_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v_imports_x3f_2029_, 1);
v___y_2012_ = v_plugins_2032_;
v___y_2013_ = v_options_2033_;
v___y_2014_ = v_name_2026_;
v___y_2015_ = v_importArts_2030_;
v___y_2016_ = v___x_2036_;
v___y_2017_ = v_package_x3f_2027_;
v___y_2018_ = v_val_2038_;
goto v___jp_2011_;
}
}
v___jp_2039_:
{
if (lean_obj_tag(v___y_2040_) == 0)
{
lean_dec_ref_known(v___y_2040_, 1);
goto v___jp_2034_;
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_options_2033_);
lean_dec_ref(v_plugins_2032_);
lean_dec(v_importArts_2030_);
lean_dec(v_imports_x3f_2029_);
lean_dec(v_package_x3f_2027_);
lean_dec(v_name_2026_);
lean_dec(v_stx_2008_);
lean_dec_ref(v_plugins_2004_);
lean_dec_ref(v___x_2003_);
lean_dec_ref(v___f_2002_);
v_a_2041_ = lean_ctor_get(v___y_2040_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___y_2040_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___y_2040_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___y_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
else
{
lean_object* v___x_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec_ref(v___f_2002_);
lean_dec(v_setup_x3f_2001_);
v___x_2060_ = lean_box(0);
v___x_2061_ = l_Lean_Elab_HeaderSyntax_isModule(v_stx_2008_);
v___x_2062_ = l_Lean_Elab_HeaderSyntax_imports(v_stx_2008_, v___x_2006_);
v___x_2063_ = lean_box(1);
v___x_2064_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2064_, 0, v_mainModuleName_2007_);
lean_ctor_set(v___x_2064_, 1, v___x_2060_);
lean_ctor_set(v___x_2064_, 2, v___x_2062_);
lean_ctor_set(v___x_2064_, 3, v___x_2003_);
lean_ctor_set(v___x_2064_, 4, v___x_2063_);
lean_ctor_set(v___x_2064_, 5, v_plugins_2004_);
lean_ctor_set_uint8(v___x_2064_, sizeof(void*)*6 + 4, v___x_2061_);
lean_ctor_set_uint32(v___x_2064_, sizeof(void*)*6, v_trustLevel_2005_);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
v___jp_2011_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2019_ = l_Lean_LeanOptions_toOptions(v___y_2013_);
v___x_2020_ = l_Lean_Options_mergeBy(v___f_2002_, v___x_2003_, v___x_2019_);
v___x_2021_ = l_Array_append___redArg(v_plugins_2004_, v___y_2012_);
lean_dec_ref(v___y_2012_);
v___x_2022_ = lean_alloc_ctor(0, 6, 5);
lean_ctor_set(v___x_2022_, 0, v___y_2014_);
lean_ctor_set(v___x_2022_, 1, v___y_2017_);
lean_ctor_set(v___x_2022_, 2, v___y_2018_);
lean_ctor_set(v___x_2022_, 3, v___x_2020_);
lean_ctor_set(v___x_2022_, 4, v___y_2015_);
lean_ctor_set(v___x_2022_, 5, v___x_2021_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*6 + 4, v___y_2016_);
lean_ctor_set_uint32(v___x_2022_, sizeof(void*)*6, v_trustLevel_2005_);
v___x_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__3___boxed(lean_object* v_setup_x3f_2067_, lean_object* v___f_2068_, lean_object* v___x_2069_, lean_object* v_plugins_2070_, lean_object* v_trustLevel_2071_, lean_object* v___x_2072_, lean_object* v_mainModuleName_2073_, lean_object* v_stx_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
uint32_t v_trustLevel_boxed_2077_; uint8_t v___x_5909__boxed_2078_; lean_object* v_res_2079_; 
v_trustLevel_boxed_2077_ = lean_unbox_uint32(v_trustLevel_2071_);
lean_dec(v_trustLevel_2071_);
v___x_5909__boxed_2078_ = lean_unbox(v___x_2072_);
v_res_2079_ = l_Lean_Elab_runFrontend___lam__3(v_setup_x3f_2067_, v___f_2068_, v___x_2069_, v_plugins_2070_, v_trustLevel_boxed_2077_, v___x_5909__boxed_2078_, v_mainModuleName_2073_, v_stx_2074_, v___y_2075_);
lean_dec_ref(v___y_2075_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4(lean_object* v_val_2080_, lean_object* v_initModIdxs_2081_, lean_object* v___x_2082_){
_start:
{
lean_object* v_cmdState_2084_; lean_object* v_env_2085_; lean_object* v___x_2086_; 
v_cmdState_2084_ = lean_ctor_get(v_val_2080_, 0);
lean_inc_ref(v_cmdState_2084_);
lean_dec_ref(v_val_2080_);
v_env_2085_ = lean_ctor_get(v_cmdState_2084_, 0);
lean_inc_ref(v_env_2085_);
lean_dec_ref(v_cmdState_2084_);
v___x_2086_ = l_Lean_runInitAttrsForModules(v_env_2085_, v_initModIdxs_2081_, v___x_2082_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___lam__4___boxed(lean_object* v_val_2087_, lean_object* v_initModIdxs_2088_, lean_object* v___x_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Lean_Elab_runFrontend___lam__4(v_val_2087_, v_initModIdxs_2088_, v___x_2089_);
lean_dec_ref(v___x_2089_);
lean_dec_ref(v_initModIdxs_2088_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__6(size_t v_sz_2092_, size_t v_i_2093_, lean_object* v_bs_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_usize_dec_lt(v_i_2093_, v_sz_2092_);
if (v___x_2095_ == 0)
{
return v_bs_2094_;
}
else
{
lean_object* v_v_2096_; lean_object* v_traces_2097_; lean_object* v___x_2098_; lean_object* v_bs_x27_2099_; size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v_v_2096_ = lean_array_uget_borrowed(v_bs_2094_, v_i_2093_);
v_traces_2097_ = lean_ctor_get(v_v_2096_, 3);
lean_inc_ref(v_traces_2097_);
v___x_2098_ = lean_unsigned_to_nat(0u);
v_bs_x27_2099_ = lean_array_uset(v_bs_2094_, v_i_2093_, v___x_2098_);
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2093_, v___x_2100_);
v___x_2102_ = lean_array_uset(v_bs_x27_2099_, v_i_2093_, v_traces_2097_);
v_i_2093_ = v___x_2101_;
v_bs_2094_ = v___x_2102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__6___boxed(lean_object* v_sz_2104_, lean_object* v_i_2105_, lean_object* v_bs_2106_){
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2104_);
lean_dec(v_sz_2104_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2105_);
lean_dec(v_i_2105_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__6(v_sz_boxed_2107_, v_i_boxed_2108_, v_bs_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(lean_object* v_as_2110_, size_t v_i_2111_, size_t v_stop_2112_, lean_object* v_b_2113_){
_start:
{
uint8_t v___x_2114_; 
v___x_2114_ = lean_usize_dec_eq(v_i_2111_, v_stop_2112_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; uint8_t v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; size_t v___x_2119_; size_t v___x_2120_; 
v___x_2115_ = lean_array_uget_borrowed(v_as_2110_, v_i_2111_);
v___x_2116_ = 2;
v___x_2117_ = lean_box(v___x_2116_);
lean_inc(v___x_2115_);
v___x_2118_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2115_, v___x_2117_, v_b_2113_);
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = lean_usize_add(v_i_2111_, v___x_2119_);
v_i_2111_ = v___x_2120_;
v_b_2113_ = v___x_2118_;
goto _start;
}
else
{
return v_b_2113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9___boxed(lean_object* v_as_2122_, lean_object* v_i_2123_, lean_object* v_stop_2124_, lean_object* v_b_2125_){
_start:
{
size_t v_i_boxed_2126_; size_t v_stop_boxed_2127_; lean_object* v_res_2128_; 
v_i_boxed_2126_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_stop_boxed_2127_ = lean_unbox_usize(v_stop_2124_);
lean_dec(v_stop_2124_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_as_2122_, v_i_boxed_2126_, v_stop_boxed_2127_, v_b_2125_);
lean_dec_ref(v_as_2122_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(lean_object* v_o_2132_, lean_object* v_k_2133_, uint8_t v_v_2134_){
_start:
{
lean_object* v_map_2135_; uint8_t v_hasTrace_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2150_; 
v_map_2135_ = lean_ctor_get(v_o_2132_, 0);
v_hasTrace_2136_ = lean_ctor_get_uint8(v_o_2132_, sizeof(void*)*1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_o_2132_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2138_ = v_o_2132_;
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_map_2135_);
lean_dec(v_o_2132_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2150_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2140_, 0, v_v_2134_);
lean_inc(v_k_2133_);
v___x_2141_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2133_, v___x_2140_, v_map_2135_);
if (v_hasTrace_2136_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; lean_object* v___x_2145_; 
v___x_2142_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___closed__1));
v___x_2143_ = l_Lean_Name_isPrefixOf(v___x_2142_, v_k_2133_);
lean_dec(v_k_2133_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2145_ = v___x_2138_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2141_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*1, v___x_2143_);
return v___x_2145_;
}
}
else
{
lean_object* v___x_2148_; 
lean_dec(v_k_2133_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2141_);
v___x_2148_ = v___x_2138_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2149_, sizeof(void*)*1, v_hasTrace_2136_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3___boxed(lean_object* v_o_2151_, lean_object* v_k_2152_, lean_object* v_v_2153_){
_start:
{
uint8_t v_v_boxed_2154_; lean_object* v_res_2155_; 
v_v_boxed_2154_ = lean_unbox(v_v_2153_);
v_res_2155_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_o_2151_, v_k_2152_, v_v_boxed_2154_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(lean_object* v_opts_2156_, lean_object* v_opt_2157_, uint8_t v_val_2158_){
_start:
{
lean_object* v_name_2159_; lean_object* v___x_2160_; 
v_name_2159_ = lean_ctor_get(v_opt_2157_, 0);
lean_inc(v_name_2159_);
lean_dec_ref(v_opt_2157_);
v___x_2160_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0_spec__3(v_opts_2156_, v_name_2159_, v_val_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0___boxed(lean_object* v_opts_2161_, lean_object* v_opt_2162_, lean_object* v_val_2163_){
_start:
{
uint8_t v_val_boxed_2164_; lean_object* v_res_2165_; 
v_val_boxed_2164_ = lean_unbox(v_val_2163_);
v_res_2165_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2161_, v_opt_2162_, v_val_boxed_2164_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(lean_object* v_opts_2166_, lean_object* v_opt_2167_, uint8_t v_val_2168_){
_start:
{
lean_object* v_name_2169_; lean_object* v_map_2170_; uint8_t v___x_2171_; 
v_name_2169_ = lean_ctor_get(v_opt_2167_, 0);
v_map_2170_ = lean_ctor_get(v_opts_2166_, 0);
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_2169_, v_map_2170_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_Option_set___at___00Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0_spec__0(v_opts_2166_, v_opt_2167_, v_val_2168_);
return v___x_2172_;
}
else
{
lean_dec_ref(v_opt_2167_);
return v_opts_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0___boxed(lean_object* v_opts_2173_, lean_object* v_opt_2174_, lean_object* v_val_2175_){
_start:
{
uint8_t v_val_boxed_2176_; lean_object* v_res_2177_; 
v_val_boxed_2176_ = lean_unbox(v_val_2175_);
v_res_2177_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2173_, v_opt_2174_, v_val_boxed_2176_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0(lean_object* v_a_2178_, lean_object* v_entries_2179_){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_task_get_own(v_a_2178_);
v___x_2181_ = l_Array_append___redArg(v_entries_2179_, v___x_2180_);
lean_dec(v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(lean_object* v_as_2182_, size_t v_sz_2183_, size_t v_i_2184_, lean_object* v_b_2185_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_usize_dec_lt(v_i_2184_, v_sz_2183_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_b_2185_);
return v___x_2188_;
}
else
{
lean_object* v___x_2189_; lean_object* v_toEnvExtension_2190_; lean_object* v_asyncMode_2191_; lean_object* v_a_2192_; lean_object* v___f_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; size_t v___x_2196_; size_t v___x_2197_; 
v___x_2189_ = l_Lean_Linter_codeQualityLogExt;
v_toEnvExtension_2190_ = lean_ctor_get(v___x_2189_, 0);
v_asyncMode_2191_ = lean_ctor_get(v_toEnvExtension_2190_, 2);
v_a_2192_ = lean_array_uget_borrowed(v_as_2182_, v_i_2184_);
lean_inc(v_a_2192_);
v___f_2193_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_2193_, 0, v_a_2192_);
v___x_2194_ = lean_box(0);
v___x_2195_ = l_Lean_PersistentEnvExtension_modifyState___redArg(v___x_2189_, v_b_2185_, v___f_2193_, v_asyncMode_2191_, v___x_2194_);
v___x_2196_ = ((size_t)1ULL);
v___x_2197_ = lean_usize_add(v_i_2184_, v___x_2196_);
v_i_2184_ = v___x_2197_;
v_b_2185_ = v___x_2195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3___boxed(lean_object* v_as_2199_, lean_object* v_sz_2200_, lean_object* v_i_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_){
_start:
{
size_t v_sz_boxed_2204_; size_t v_i_boxed_2205_; lean_object* v_res_2206_; 
v_sz_boxed_2204_ = lean_unbox_usize(v_sz_2200_);
lean_dec(v_sz_2200_);
v_i_boxed_2205_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_res_2206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_as_2199_, v_sz_boxed_2204_, v_i_boxed_2205_, v_b_2202_);
lean_dec_ref(v_as_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(lean_object* v_s_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = l_Lean_Language_Snapshot_transform(v_s_2209_, v___y_2210_);
v___x_2212_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___closed__0));
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2211_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0___boxed(lean_object* v_s_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___lam__0(v_s_2214_, v___y_2215_);
lean_dec_ref(v___y_2215_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(lean_object* v_t_2218_, lean_object* v_a_2219_){
_start:
{
lean_object* v___f_2220_; lean_object* v___x_2221_; 
v___f_2220_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___closed__0));
v___x_2221_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2218_, v___f_2220_, v_a_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3___boxed(lean_object* v_t_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_t_2222_, v_a_2223_);
lean_dec_ref(v_a_2223_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(lean_object* v_t_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___closed__0));
v___x_2229_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2226_, v___x_2228_, v_a_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8___boxed(lean_object* v_t_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_t_2230_, v_a_2231_);
lean_dec_ref(v_a_2231_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(lean_object* v_s_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_toSnapshot_2235_; lean_object* v_metaSnap_2236_; lean_object* v_result_x3f_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___y_2241_; 
v_toSnapshot_2235_ = lean_ctor_get(v_s_2233_, 0);
lean_inc_ref(v_toSnapshot_2235_);
v_metaSnap_2236_ = lean_ctor_get(v_s_2233_, 1);
lean_inc_ref(v_metaSnap_2236_);
v_result_x3f_2237_ = lean_ctor_get(v_s_2233_, 2);
lean_inc(v_result_x3f_2237_);
lean_dec_ref(v_s_2233_);
v___x_2238_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2235_, v___y_2234_);
v___x_2239_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2236_, v___y_2234_);
if (lean_obj_tag(v_result_x3f_2237_) == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = lean_box(0);
v___y_2241_ = v___x_2247_;
goto v___jp_2240_;
}
else
{
lean_object* v_val_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2257_; 
v_val_2248_ = lean_ctor_get(v_result_x3f_2237_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_result_x3f_2237_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2250_ = v_result_x3f_2237_;
v_isShared_2251_ = v_isSharedCheck_2257_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_val_2248_);
lean_dec(v_result_x3f_2237_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2257_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_firstCmdSnap_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v_firstCmdSnap_2252_ = lean_ctor_get(v_val_2248_, 1);
lean_inc_ref(v_firstCmdSnap_2252_);
lean_dec(v_val_2248_);
v___x_2253_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4_spec__8(v_firstCmdSnap_2252_, v___y_2234_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2253_);
v___x_2255_ = v___x_2250_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
v___y_2241_ = v___x_2255_;
goto v___jp_2240_;
}
}
}
v___jp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2242_ = lean_unsigned_to_nat(1u);
v___x_2243_ = lean_mk_empty_array_with_capacity(v___x_2242_);
v___x_2244_ = lean_array_push(v___x_2243_, v___x_2239_);
v___x_2245_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2241_, v___x_2244_);
v___x_2246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2238_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
return v___x_2246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0___boxed(lean_object* v_s_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___lam__0(v_s_2258_, v___y_2259_);
lean_dec_ref(v___y_2259_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(lean_object* v_t_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___f_2264_; lean_object* v___x_2265_; 
v___f_2264_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___closed__0));
v___x_2265_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_2262_, v___f_2264_, v_a_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4___boxed(lean_object* v_t_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_t_2266_, v_a_2267_);
lean_dec_ref(v_a_2267_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(lean_object* v_a_2269_){
_start:
{
lean_object* v_toSnapshot_2270_; lean_object* v_metaSnap_2271_; lean_object* v_result_x3f_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___y_2277_; 
v_toSnapshot_2270_ = lean_ctor_get(v_a_2269_, 0);
lean_inc_ref(v_toSnapshot_2270_);
v_metaSnap_2271_ = lean_ctor_get(v_a_2269_, 1);
lean_inc_ref(v_metaSnap_2271_);
v_result_x3f_2272_ = lean_ctor_get(v_a_2269_, 4);
lean_inc(v_result_x3f_2272_);
lean_dec_ref(v_a_2269_);
v___x_2273_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_2274_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_2270_, v___x_2273_);
v___x_2275_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__3(v_metaSnap_2271_, v___x_2273_);
if (lean_obj_tag(v_result_x3f_2272_) == 0)
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_box(0);
v___y_2277_ = v___x_2283_;
goto v___jp_2276_;
}
else
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2293_; 
v_val_2284_ = lean_ctor_get(v_result_x3f_2272_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_result_x3f_2272_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2286_ = v_result_x3f_2272_;
v_isShared_2287_ = v_isSharedCheck_2293_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v_result_x3f_2272_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2293_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_processedSnap_2288_; lean_object* v___x_2289_; lean_object* v___x_2291_; 
v_processedSnap_2288_ = lean_ctor_get(v_val_2284_, 1);
lean_inc_ref(v_processedSnap_2288_);
lean_dec(v_val_2284_);
v___x_2289_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2_spec__4(v_processedSnap_2288_, v___x_2273_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2289_);
v___x_2291_ = v___x_2286_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
v___y_2277_ = v___x_2291_;
goto v___jp_2276_;
}
}
}
v___jp_2276_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2278_ = lean_unsigned_to_nat(1u);
v___x_2279_ = lean_mk_empty_array_with_capacity(v___x_2278_);
v___x_2280_ = lean_array_push(v___x_2279_, v___x_2275_);
v___x_2281_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_2277_, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2274_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(lean_object* v_as_2294_, size_t v_i_2295_, size_t v_stop_2296_, lean_object* v_b_2297_){
_start:
{
lean_object* v___y_2299_; uint8_t v___x_2303_; 
v___x_2303_ = lean_usize_dec_eq(v_i_2295_, v_stop_2296_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v_infoTree_x3f_2305_; 
v___x_2304_ = lean_array_uget_borrowed(v_as_2294_, v_i_2295_);
v_infoTree_x3f_2305_ = lean_ctor_get(v___x_2304_, 2);
if (lean_obj_tag(v_infoTree_x3f_2305_) == 1)
{
lean_object* v_val_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v_val_2306_ = lean_ctor_get(v_infoTree_x3f_2305_, 0);
v___x_2307_ = lean_unsigned_to_nat(1u);
v___x_2308_ = lean_mk_empty_array_with_capacity(v___x_2307_);
lean_inc(v_val_2306_);
v___x_2309_ = lean_array_push(v___x_2308_, v_val_2306_);
v___x_2310_ = l_Array_append___redArg(v_b_2297_, v___x_2309_);
lean_dec_ref(v___x_2309_);
v___y_2299_ = v___x_2310_;
goto v___jp_2298_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Frontend_0__Lean_Elab_IO_processCommandsIncrementally_go_spec__1___closed__0));
v___x_2312_ = l_Array_append___redArg(v_b_2297_, v___x_2311_);
v___y_2299_ = v___x_2312_;
goto v___jp_2298_;
}
}
else
{
return v_b_2297_;
}
v___jp_2298_:
{
size_t v___x_2300_; size_t v___x_2301_; 
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2295_, v___x_2300_);
v_i_2295_ = v___x_2301_;
v_b_2297_ = v___y_2299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8___boxed(lean_object* v_as_2313_, lean_object* v_i_2314_, lean_object* v_stop_2315_, lean_object* v_b_2316_){
_start:
{
size_t v_i_boxed_2317_; size_t v_stop_boxed_2318_; lean_object* v_res_2319_; 
v_i_boxed_2317_ = lean_unbox_usize(v_i_2314_);
lean_dec(v_i_2314_);
v_stop_boxed_2318_ = lean_unbox_usize(v_stop_2315_);
lean_dec(v_stop_2315_);
v_res_2319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v_as_2313_, v_i_boxed_2317_, v_stop_boxed_2318_, v_b_2316_);
lean_dec_ref(v_as_2313_);
return v_res_2319_;
}
}
static double _init_l_Lean_Elab_runFrontend___closed__1(void){
_start:
{
lean_object* v___x_2321_; double v___x_2322_; 
v___x_2321_ = lean_unsigned_to_nat(1000000000u);
v___x_2322_ = lean_float_of_nat(v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend(lean_object* v_input_2324_, lean_object* v_opts_2325_, lean_object* v_fileName_2326_, lean_object* v_mainModuleName_2327_, uint32_t v_trustLevel_2328_, lean_object* v_oleanFileName_x3f_2329_, lean_object* v_ileanFileName_x3f_2330_, uint8_t v_jsonOutput_2331_, lean_object* v_errorOnKinds_2332_, lean_object* v_plugins_2333_, uint8_t v_printStats_2334_, lean_object* v_setup_x3f_2335_, lean_object* v_incrSaveFileName_x3f_2336_, lean_object* v_incrLoadFileName_x3f_2337_, lean_object* v_incrHeaderSaveFileName_x3f_2338_){
_start:
{
lean_object* v___y_2341_; lean_object* v___y_2342_; lean_object* v___x_2346_; lean_object* v___f_2347_; lean_object* v___x_2348_; double v___x_2349_; double v___x_2350_; double v___x_2351_; uint8_t v___x_2352_; lean_object* v___y_2354_; lean_object* v___y_2355_; size_t v___y_2356_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___y_2417_; lean_object* v___y_2418_; lean_object* v___y_2419_; uint8_t v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; size_t v___y_2423_; lean_object* v___y_2424_; lean_object* v___y_2425_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; uint8_t v___y_2460_; lean_object* v___y_2461_; size_t v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___y_2473_; lean_object* v___y_2474_; uint8_t v___y_2475_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; uint8_t v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; size_t v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2506_; lean_object* v___y_2507_; uint8_t v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; uint8_t v___y_2512_; lean_object* v___y_2513_; size_t v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v___y_2529_; uint8_t v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; uint8_t v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; size_t v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v_a_2612_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v___y_2633_; 
v___x_2346_ = lean_io_mono_nanos_now();
v___f_2347_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__0));
v___x_2348_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2349_ = lean_float_of_nat(v___x_2346_);
v___x_2350_ = lean_float_once(&l_Lean_Elab_runFrontend___closed__1, &l_Lean_Elab_runFrontend___closed__1_once, _init_l_Lean_Elab_runFrontend___closed__1);
v___x_2351_ = lean_float_div(v___x_2349_, v___x_2350_);
v___x_2352_ = 1;
v___x_2414_ = lean_string_utf8_byte_size(v_input_2324_);
v___x_2415_ = l_Lean_Parser_mkInputContext___redArg(v_input_2324_, v_fileName_2326_, v___x_2352_, v___x_2414_);
v___x_2631_ = l_Lean_internal_cmdlineSnapshots;
if (lean_obj_tag(v_incrSaveFileName_x3f_2336_) == 0)
{
v___y_2633_ = v___x_2352_;
goto v___jp_2632_;
}
else
{
uint8_t v___x_2669_; 
v___x_2669_ = 0;
v___y_2633_ = v___x_2669_;
goto v___jp_2632_;
}
v___jp_2340_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = lean_runtime_forget(v___y_2342_);
v___x_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___y_2341_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
v___jp_2353_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = l_Lean_trace_profiler_output;
v___x_2360_ = l_Lean_Option_get_x3f___at___00Lean_Elab_runFrontend_spec__5(v___y_2357_, v___x_2359_);
if (lean_obj_tag(v___x_2360_) == 1)
{
lean_object* v_val_2361_; lean_object* v___x_2362_; size_t v_sz_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec_ref(v___y_2355_);
v_val_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_val_2361_);
lean_dec_ref_known(v___x_2360_, 1);
lean_inc_ref(v___y_2358_);
v___x_2362_ = l_Lean_Language_SnapshotTree_getAll(v___y_2358_);
v_sz_2363_ = lean_array_size(v___x_2362_);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__6(v_sz_2363_, v___y_2356_, v___x_2362_);
v___x_2365_ = l_Lean_Name_toString(v_mainModuleName_2327_, v___x_2352_);
v___x_2366_ = l_Lean_Firefox_Profile_export(v___x_2365_, v___x_2351_, v___x_2364_, v___y_2357_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v___x_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2367_);
v___x_2369_ = l_Lean_Json_compress(v___x_2368_);
v___x_2370_ = l_IO_FS_writeFile(v_val_2361_, v___x_2369_);
lean_dec_ref(v___x_2369_);
lean_dec(v_val_2361_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_dec_ref_known(v___x_2370_, 1);
v___y_2341_ = v___y_2354_;
v___y_2342_ = v___y_2358_;
goto v___jp_2340_;
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v___y_2358_);
lean_dec_ref(v___y_2354_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
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
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_val_2361_);
lean_dec_ref(v___y_2358_);
lean_dec_ref(v___y_2354_);
v_a_2379_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2366_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2366_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
lean_dec(v___x_2360_);
v___x_2387_ = l_Lean_trace_profiler_serve;
v___x_2388_ = l_Lean_Option_get___at___00Lean_Elab_runFrontend_spec__7(v___y_2355_, v___x_2387_);
lean_dec_ref(v___y_2355_);
if (v___x_2388_ == 0)
{
lean_dec_ref(v___y_2357_);
lean_dec(v_mainModuleName_2327_);
v___y_2341_ = v___y_2354_;
v___y_2342_ = v___y_2358_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2389_; size_t v_sz_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
lean_inc_ref(v___y_2358_);
v___x_2389_ = l_Lean_Language_SnapshotTree_getAll(v___y_2358_);
v_sz_2390_ = lean_array_size(v___x_2389_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_runFrontend_spec__6(v_sz_2390_, v___y_2356_, v___x_2389_);
v___x_2392_ = l_Lean_Name_toString(v_mainModuleName_2327_, v___x_2352_);
v___x_2393_ = l_Lean_Firefox_Profile_export(v___x_2392_, v___x_2351_, v___x_2391_, v___y_2357_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v___x_2391_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = l_Lean_Firefox_instToJsonProfile_toJson(v_a_2394_);
v___x_2396_ = l_Lean_Json_compress(v___x_2395_);
v___x_2397_ = l_Lean_Firefox_Profile_serve(v___x_2396_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_dec_ref_known(v___x_2397_, 1);
v___y_2341_ = v___y_2354_;
v___y_2342_ = v___y_2358_;
goto v___jp_2340_;
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v___y_2358_);
lean_dec_ref(v___y_2354_);
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v___y_2358_);
lean_dec_ref(v___y_2354_);
v_a_2406_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2393_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2393_);
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
v___jp_2416_:
{
lean_object* v_fileMap_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v_stx_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2451_; 
v_fileMap_2426_ = lean_ctor_get(v___x_2415_, 2);
lean_inc_ref(v_fileMap_2426_);
lean_dec_ref(v___x_2415_);
v___x_2427_ = l_Lean_Server_findModuleRefs(v_fileMap_2426_, v___y_2425_, v___y_2420_, v___y_2420_);
lean_dec_ref(v___y_2425_);
v___x_2428_ = l_Lean_Server_ModuleRefs_toLspModuleRefs(v___x_2427_);
v_fst_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_fst_2429_);
v_snd_2430_ = lean_ctor_get(v___x_2428_, 1);
lean_inc(v_snd_2430_);
lean_dec_ref(v___x_2428_);
v_stx_2431_ = lean_ctor_get(v___y_2421_, 3);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___y_2421_);
if (v_isSharedCheck_2451_ == 0)
{
lean_object* v_unused_2452_; lean_object* v_unused_2453_; lean_object* v_unused_2454_; lean_object* v_unused_2455_; 
v_unused_2452_ = lean_ctor_get(v___y_2421_, 4);
lean_dec(v_unused_2452_);
v_unused_2453_ = lean_ctor_get(v___y_2421_, 2);
lean_dec(v_unused_2453_);
v_unused_2454_ = lean_ctor_get(v___y_2421_, 1);
lean_dec(v_unused_2454_);
v_unused_2455_ = lean_ctor_get(v___y_2421_, 0);
lean_dec(v_unused_2455_);
v___x_2433_ = v___y_2421_;
v_isShared_2434_ = v_isSharedCheck_2451_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_stx_2431_);
lean_dec(v___y_2421_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2451_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2435_ = lean_unsigned_to_nat(5u);
v___x_2436_ = l_Lean_Server_collectImports(v_stx_2431_);
lean_inc(v_mainModuleName_2327_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 4, v_snd_2430_);
lean_ctor_set(v___x_2433_, 3, v_fst_2429_);
lean_ctor_set(v___x_2433_, 2, v___x_2436_);
lean_ctor_set(v___x_2433_, 1, v_mainModuleName_2327_);
lean_ctor_set(v___x_2433_, 0, v___x_2435_);
v___x_2438_ = v___x_2433_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_mainModuleName_2327_);
lean_ctor_set(v_reuseFailAlloc_2450_, 2, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2450_, 3, v_fst_2429_);
lean_ctor_set(v_reuseFailAlloc_2450_, 4, v_snd_2430_);
v___x_2438_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = l_Lean_Server_instToJsonIlean_toJson(v___x_2438_);
v___x_2440_ = l_Lean_Json_compress(v___x_2439_);
v___x_2441_ = l_IO_FS_writeFile(v___y_2419_, v___x_2440_);
lean_dec_ref(v___x_2440_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_dec_ref_known(v___x_2441_, 1);
v___y_2354_ = v___y_2417_;
v___y_2355_ = v___y_2418_;
v___y_2356_ = v___y_2423_;
v___y_2357_ = v___y_2422_;
v___y_2358_ = v___y_2424_;
goto v___jp_2353_;
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v___y_2424_);
lean_dec_ref(v___y_2422_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v_mainModuleName_2327_);
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
}
v___jp_2456_:
{
if (lean_obj_tag(v_ileanFileName_x3f_2330_) == 1)
{
lean_object* v_val_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v_val_2465_ = lean_ctor_get(v_ileanFileName_x3f_2330_, 0);
lean_inc_ref(v___y_2464_);
v___x_2466_ = l_Lean_Language_SnapshotTree_getAll(v___y_2464_);
v___x_2467_ = lean_mk_empty_array_with_capacity(v___y_2458_);
v___x_2468_ = lean_array_get_size(v___x_2466_);
v___x_2469_ = lean_nat_dec_lt(v___y_2458_, v___x_2468_);
lean_dec(v___y_2458_);
if (v___x_2469_ == 0)
{
lean_dec_ref(v___x_2466_);
v___y_2417_ = v___y_2457_;
v___y_2418_ = v___y_2459_;
v___y_2419_ = v_val_2465_;
v___y_2420_ = v___y_2460_;
v___y_2421_ = v___y_2461_;
v___y_2422_ = v___y_2463_;
v___y_2423_ = v___y_2462_;
v___y_2424_ = v___y_2464_;
v___y_2425_ = v___x_2467_;
goto v___jp_2416_;
}
else
{
size_t v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_usize_of_nat(v___x_2468_);
v___x_2471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__8(v___x_2466_, v___y_2462_, v___x_2470_, v___x_2467_);
lean_dec_ref(v___x_2466_);
v___y_2417_ = v___y_2457_;
v___y_2418_ = v___y_2459_;
v___y_2419_ = v_val_2465_;
v___y_2420_ = v___y_2460_;
v___y_2421_ = v___y_2461_;
v___y_2422_ = v___y_2463_;
v___y_2423_ = v___y_2462_;
v___y_2424_ = v___y_2464_;
v___y_2425_ = v___x_2471_;
goto v___jp_2416_;
}
}
else
{
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2458_);
lean_dec_ref(v___x_2415_);
v___y_2354_ = v___y_2457_;
v___y_2355_ = v___y_2459_;
v___y_2356_ = v___y_2462_;
v___y_2357_ = v___y_2463_;
v___y_2358_ = v___y_2464_;
goto v___jp_2353_;
}
}
v___jp_2472_:
{
if (v___y_2479_ == 0)
{
if (lean_obj_tag(v_oleanFileName_x3f_2329_) == 1)
{
lean_object* v_val_2484_; lean_object* v_fileMap_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_val_2484_ = lean_ctor_get(v_oleanFileName_x3f_2329_, 0);
lean_inc(v_val_2484_);
lean_dec_ref_known(v_oleanFileName_x3f_2329_, 1);
v_fileMap_2485_ = lean_ctor_get(v___x_2415_, 2);
lean_inc_ref(v_fileMap_2485_);
v___x_2486_ = ((lean_object*)(l_Lean_Elab_runFrontend___closed__2));
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_mk_empty_array_with_capacity(v___y_2478_);
lean_inc_ref(v___y_2483_);
v___x_2489_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_collectCommandLints(v___y_2483_, v___x_2487_, v___x_2488_);
v___x_2490_ = lean_box(v___x_2352_);
v___x_2491_ = lean_box(v___y_2475_);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__2___boxed), 8, 7);
lean_closure_set(v___f_2492_, 0, v_fileMap_2485_);
lean_closure_set(v___f_2492_, 1, v___y_2473_);
lean_closure_set(v___f_2492_, 2, v___x_2489_);
lean_closure_set(v___f_2492_, 3, v___y_2474_);
lean_closure_set(v___f_2492_, 4, v_val_2484_);
lean_closure_set(v___f_2492_, 5, v___x_2490_);
lean_closure_set(v___f_2492_, 6, v___x_2491_);
v___x_2493_ = lean_box(0);
v___x_2494_ = l_Lean_profileitIOUnsafe___redArg(v___x_2486_, v___y_2477_, v___f_2492_, v___x_2493_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_dec_ref_known(v___x_2494_, 1);
v___y_2457_ = v___y_2476_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2477_;
v___y_2460_ = v___y_2479_;
v___y_2461_ = v___y_2480_;
v___y_2462_ = v___y_2482_;
v___y_2463_ = v___y_2481_;
v___y_2464_ = v___y_2483_;
goto v___jp_2456_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v___y_2483_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___x_2415_);
lean_dec(v_mainModuleName_2327_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2494_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2494_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v_oleanFileName_x3f_2329_);
v___y_2457_ = v___y_2476_;
v___y_2458_ = v___y_2478_;
v___y_2459_ = v___y_2477_;
v___y_2460_ = v___y_2479_;
v___y_2461_ = v___y_2480_;
v___y_2462_ = v___y_2482_;
v___y_2463_ = v___y_2481_;
v___y_2464_ = v___y_2483_;
goto v___jp_2456_;
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec_ref(v___y_2483_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec_ref(v___x_2415_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
v___jp_2505_:
{
if (v_printStats_2334_ == 0)
{
v___y_2473_ = v___y_2506_;
v___y_2474_ = v___y_2507_;
v___y_2475_ = v___y_2508_;
v___y_2476_ = v___y_2509_;
v___y_2477_ = v___y_2511_;
v___y_2478_ = v___y_2510_;
v___y_2479_ = v___y_2512_;
v___y_2480_ = v___y_2513_;
v___y_2481_ = v___y_2515_;
v___y_2482_ = v___y_2514_;
v___y_2483_ = v___y_2516_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2517_; 
lean_inc_ref(v___y_2509_);
v___x_2517_ = l_Lean_Environment_displayStats(v___y_2509_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_dec_ref_known(v___x_2517_, 1);
v___y_2473_ = v___y_2506_;
v___y_2474_ = v___y_2507_;
v___y_2475_ = v___y_2508_;
v___y_2476_ = v___y_2509_;
v___y_2477_ = v___y_2511_;
v___y_2478_ = v___y_2510_;
v___y_2479_ = v___y_2512_;
v___y_2480_ = v___y_2513_;
v___y_2481_ = v___y_2515_;
v___y_2482_ = v___y_2514_;
v___y_2483_ = v___y_2516_;
goto v___jp_2472_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec_ref(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec_ref(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec_ref(v___x_2415_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
v___jp_2526_:
{
if (lean_obj_tag(v_incrHeaderSaveFileName_x3f_2338_) == 1)
{
lean_object* v_val_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v_val_2538_ = lean_ctor_get(v_incrHeaderSaveFileName_x3f_2338_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v_incrHeaderSaveFileName_x3f_2338_, 1);
lean_inc_ref(v___y_2534_);
v___x_2539_ = l_Lean_Language_Lean_truncateToHeader(v___y_2534_);
v___x_2540_ = lean_apply_3(v___y_2529_, v_val_2538_, v___x_2539_, lean_box(0));
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_dec_ref_known(v___x_2540_, 1);
lean_inc_ref(v___y_2528_);
v___y_2506_ = v___y_2527_;
v___y_2507_ = v___y_2528_;
v___y_2508_ = v___y_2530_;
v___y_2509_ = v___y_2531_;
v___y_2510_ = v___y_2532_;
v___y_2511_ = v___y_2528_;
v___y_2512_ = v___y_2533_;
v___y_2513_ = v___y_2534_;
v___y_2514_ = v___y_2536_;
v___y_2515_ = v___y_2535_;
v___y_2516_ = v___y_2537_;
goto v___jp_2505_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v___y_2537_);
lean_dec_ref(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec_ref(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v___x_2415_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_dec_ref(v___y_2529_);
lean_dec(v_incrHeaderSaveFileName_x3f_2338_);
lean_inc_ref(v___y_2528_);
v___y_2506_ = v___y_2527_;
v___y_2507_ = v___y_2528_;
v___y_2508_ = v___y_2530_;
v___y_2509_ = v___y_2531_;
v___y_2510_ = v___y_2532_;
v___y_2511_ = v___y_2528_;
v___y_2512_ = v___y_2533_;
v___y_2513_ = v___y_2534_;
v___y_2514_ = v___y_2536_;
v___y_2515_ = v___y_2535_;
v___y_2516_ = v___y_2537_;
goto v___jp_2505_;
}
}
v___jp_2549_:
{
lean_object* v___x_2555_; 
lean_inc_ref(v___y_2553_);
v___x_2555_ = l_Lean_Language_SnapshotTree_runAndReport(v___y_2553_, v___y_2552_, v_jsonOutput_2331_, v___y_2554_);
lean_dec(v___y_2554_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2600_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2600_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2600_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2560_; 
lean_inc_ref(v___y_2551_);
v___x_2560_ = l_Lean_Language_Lean_waitForFinalCmdState_x3f(v___y_2551_);
if (lean_obj_tag(v___x_2560_) == 1)
{
lean_object* v_val_2561_; lean_object* v_env_2562_; lean_object* v_scopes_2563_; lean_object* v_codeQualityEntryTasks_2564_; size_t v_sz_2565_; size_t v___x_2566_; lean_object* v___x_2567_; 
lean_del_object(v___x_2558_);
v_val_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_val_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v_env_2562_ = lean_ctor_get(v_val_2561_, 0);
lean_inc_ref(v_env_2562_);
v_scopes_2563_ = lean_ctor_get(v_val_2561_, 2);
lean_inc(v_scopes_2563_);
v_codeQualityEntryTasks_2564_ = lean_ctor_get(v_val_2561_, 12);
lean_inc_ref(v_codeQualityEntryTasks_2564_);
lean_dec(v_val_2561_);
v_sz_2565_ = lean_array_size(v_codeQualityEntryTasks_2564_);
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_runFrontend_spec__3(v_codeQualityEntryTasks_2564_, v_sz_2565_, v___x_2566_, v_env_2562_);
lean_dec_ref(v_codeQualityEntryTasks_2564_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; lean_object* v_opts_2570_; lean_object* v___x_2571_; lean_object* v___f_2572_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_n(v_a_2568_, 2);
lean_dec_ref_known(v___x_2567_, 1);
lean_inc(v___y_2550_);
v___x_2569_ = l_List_get_x21Internal___redArg(v___x_2348_, v_scopes_2563_, v___y_2550_);
lean_dec(v_scopes_2563_);
v_opts_2570_ = lean_ctor_get(v___x_2569_, 1);
lean_inc_ref(v_opts_2570_);
lean_dec(v___x_2569_);
v___x_2571_ = lean_box(v___x_2352_);
v___f_2572_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2572_, 0, v_a_2568_);
lean_closure_set(v___f_2572_, 1, v___x_2571_);
if (lean_obj_tag(v_incrSaveFileName_x3f_2336_) == 1)
{
lean_object* v_val_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_val_2573_ = lean_ctor_get(v_incrSaveFileName_x3f_2336_, 0);
lean_inc(v_val_2573_);
lean_dec_ref_known(v_incrSaveFileName_x3f_2336_, 1);
v___x_2574_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_resolveCancelTokensForSave(v___y_2553_);
lean_inc_ref(v___y_2551_);
v___x_2575_ = l_Lean_Elab_runFrontend___lam__1(v_a_2568_, v___x_2352_, v_val_2573_, v___y_2551_);
if (lean_obj_tag(v___x_2575_) == 0)
{
uint8_t v___x_2576_; uint8_t v___x_2577_; 
lean_dec_ref_known(v___x_2575_, 1);
v___x_2576_ = lean_unbox(v_a_2556_);
v___x_2577_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
lean_inc(v_a_2568_);
v___y_2527_ = v_a_2568_;
v___y_2528_ = v_opts_2570_;
v___y_2529_ = v___f_2572_;
v___y_2530_ = v___x_2576_;
v___y_2531_ = v_a_2568_;
v___y_2532_ = v___y_2550_;
v___y_2533_ = v___x_2577_;
v___y_2534_ = v___y_2551_;
v___y_2535_ = v___y_2552_;
v___y_2536_ = v___x_2566_;
v___y_2537_ = v___y_2553_;
goto v___jp_2526_;
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v___f_2572_);
lean_dec_ref(v_opts_2570_);
lean_dec(v_a_2568_);
lean_dec(v_a_2556_);
lean_dec_ref(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___x_2415_);
lean_dec(v_incrHeaderSaveFileName_x3f_2338_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v_a_2578_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2575_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2575_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
else
{
uint8_t v___x_2586_; uint8_t v___x_2587_; 
lean_dec(v_incrSaveFileName_x3f_2336_);
v___x_2586_ = lean_unbox(v_a_2556_);
v___x_2587_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
lean_inc(v_a_2568_);
v___y_2527_ = v_a_2568_;
v___y_2528_ = v_opts_2570_;
v___y_2529_ = v___f_2572_;
v___y_2530_ = v___x_2586_;
v___y_2531_ = v_a_2568_;
v___y_2532_ = v___y_2550_;
v___y_2533_ = v___x_2587_;
v___y_2534_ = v___y_2551_;
v___y_2535_ = v___y_2552_;
v___y_2536_ = v___x_2566_;
v___y_2537_ = v___y_2553_;
goto v___jp_2526_;
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_scopes_2563_);
lean_dec(v_a_2556_);
lean_dec_ref(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___x_2415_);
lean_dec(v_incrHeaderSaveFileName_x3f_2338_);
lean_dec(v_incrSaveFileName_x3f_2336_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v_a_2588_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2567_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2567_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_object* v___x_2596_; lean_object* v___x_2598_; 
lean_dec(v___x_2560_);
lean_dec(v_a_2556_);
lean_dec_ref(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___x_2415_);
lean_dec(v_incrHeaderSaveFileName_x3f_2338_);
lean_dec(v_incrSaveFileName_x3f_2336_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v___x_2596_ = lean_box(0);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 0, v___x_2596_);
v___x_2598_ = v___x_2558_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
lean_dec_ref(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___x_2415_);
lean_dec(v_incrHeaderSaveFileName_x3f_2338_);
lean_dec(v_incrSaveFileName_x3f_2336_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v_a_2601_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2555_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2555_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
v___jp_2609_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2613_ = l_Lean_Language_Lean_process(v___y_2611_, v_a_2612_, v___x_2415_);
lean_inc_ref(v___x_2613_);
v___x_2614_ = l_Lean_Language_toSnapshotTree___at___00Lean_Elab_runFrontend_spec__2(v___x_2613_);
v___x_2615_ = lean_box(1);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_array_get_size(v_errorOnKinds_2332_);
v___x_2618_ = lean_nat_dec_lt(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
v___y_2550_ = v___x_2616_;
v___y_2551_ = v___x_2613_;
v___y_2552_ = v___y_2610_;
v___y_2553_ = v___x_2614_;
v___y_2554_ = v___x_2615_;
goto v___jp_2549_;
}
else
{
uint8_t v___x_2619_; 
v___x_2619_ = lean_nat_dec_le(v___x_2617_, v___x_2617_);
if (v___x_2619_ == 0)
{
if (v___x_2618_ == 0)
{
v___y_2550_ = v___x_2616_;
v___y_2551_ = v___x_2613_;
v___y_2552_ = v___y_2610_;
v___y_2553_ = v___x_2614_;
v___y_2554_ = v___x_2615_;
goto v___jp_2549_;
}
else
{
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = ((size_t)0ULL);
v___x_2621_ = lean_usize_of_nat(v___x_2617_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2332_, v___x_2620_, v___x_2621_, v___x_2615_);
v___y_2550_ = v___x_2616_;
v___y_2551_ = v___x_2613_;
v___y_2552_ = v___y_2610_;
v___y_2553_ = v___x_2614_;
v___y_2554_ = v___x_2622_;
goto v___jp_2549_;
}
}
else
{
size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = ((size_t)0ULL);
v___x_2624_ = lean_usize_of_nat(v___x_2617_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_runFrontend_spec__9(v_errorOnKinds_2332_, v___x_2623_, v___x_2624_, v___x_2615_);
v___y_2550_ = v___x_2616_;
v___y_2551_ = v___x_2613_;
v___y_2552_ = v___y_2610_;
v___y_2553_ = v___x_2614_;
v___y_2554_ = v___x_2625_;
goto v___jp_2549_;
}
}
}
v___jp_2626_:
{
lean_object* v___x_2630_; 
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v_a_2629_);
v___y_2610_ = v___y_2627_;
v___y_2611_ = v___y_2628_;
v_a_2612_ = v___x_2630_;
goto v___jp_2609_;
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___f_2639_; 
v___x_2634_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v_opts_2325_, v___x_2631_, v___y_2633_);
v___x_2635_ = l_Lean_Elab_async;
v___x_2636_ = l_Lean_Option_setIfNotSet___at___00Lean_Elab_runFrontend_spec__0(v___x_2634_, v___x_2635_, v___x_2352_);
v___x_2637_ = lean_box_uint32(v_trustLevel_2328_);
v___x_2638_ = lean_box(v___x_2352_);
lean_inc(v_mainModuleName_2327_);
lean_inc_ref(v___x_2636_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__3___boxed), 10, 7);
lean_closure_set(v___f_2639_, 0, v_setup_x3f_2335_);
lean_closure_set(v___f_2639_, 1, v___f_2347_);
lean_closure_set(v___f_2639_, 2, v___x_2636_);
lean_closure_set(v___f_2639_, 3, v_plugins_2333_);
lean_closure_set(v___f_2639_, 4, v___x_2637_);
lean_closure_set(v___f_2639_, 5, v___x_2638_);
lean_closure_set(v___f_2639_, 6, v_mainModuleName_2327_);
if (lean_obj_tag(v_incrLoadFileName_x3f_2337_) == 0)
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_box(0);
v___y_2610_ = v___x_2636_;
v___y_2611_ = v___f_2639_;
v_a_2612_ = v___x_2640_;
goto v___jp_2609_;
}
else
{
lean_object* v_val_2641_; lean_object* v___x_2642_; 
v_val_2641_ = lean_ctor_get(v_incrLoadFileName_x3f_2337_, 0);
lean_inc(v_val_2641_);
lean_dec_ref_known(v_incrLoadFileName_x3f_2337_, 1);
v___x_2642_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_loadIncrSnapshot(v_val_2641_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v_snap_2644_; lean_object* v_initModIdxs_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v_snap_2644_ = lean_ctor_get(v_a_2643_, 0);
lean_inc_ref(v_snap_2644_);
v_initModIdxs_2645_ = lean_ctor_get(v_a_2643_, 1);
lean_inc_ref(v_initModIdxs_2645_);
lean_dec(v_a_2643_);
lean_inc(v_mainModuleName_2327_);
v___x_2646_ = l___private_Lean_Elab_Frontend_0__Lean_Elab_setMainModule(v_snap_2644_, v_mainModuleName_2327_);
lean_inc_ref(v___x_2646_);
v___x_2647_ = l_Lean_Language_Lean_HeaderParsedSnapshot_processedResult(v___x_2646_);
v___x_2648_ = l_Lean_Language_SnapshotTask_get___redArg(v___x_2647_);
if (lean_obj_tag(v___x_2648_) == 1)
{
lean_object* v_val_2649_; lean_object* v___f_2650_; lean_object* v___x_2651_; 
v_val_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_val_2649_);
lean_dec_ref_known(v___x_2648_, 1);
lean_inc_ref(v___x_2636_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_Elab_runFrontend___lam__4___boxed), 4, 3);
lean_closure_set(v___f_2650_, 0, v_val_2649_);
lean_closure_set(v___f_2650_, 1, v_initModIdxs_2645_);
lean_closure_set(v___f_2650_, 2, v___x_2636_);
v___x_2651_ = l_Lean_withImporting___redArg(v___f_2650_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2652_; 
lean_dec_ref_known(v___x_2651_, 1);
v___x_2652_ = lean_enable_initializer_execution();
v___y_2627_ = v___x_2636_;
v___y_2628_ = v___f_2639_;
v_a_2629_ = v___x_2646_;
goto v___jp_2626_;
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v___x_2646_);
lean_dec_ref(v___f_2639_);
lean_dec_ref(v___x_2636_);
lean_dec_ref(v___x_2415_);
lean_dec(v_incrHeaderSaveFileName_x3f_2338_);
lean_dec(v_incrSaveFileName_x3f_2336_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v_a_2653_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2651_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2651_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_dec(v___x_2648_);
lean_dec_ref(v_initModIdxs_2645_);
v___y_2627_ = v___x_2636_;
v___y_2628_ = v___f_2639_;
v_a_2629_ = v___x_2646_;
goto v___jp_2626_;
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v___f_2639_);
lean_dec_ref(v___x_2636_);
lean_dec_ref(v___x_2415_);
lean_dec(v_incrHeaderSaveFileName_x3f_2338_);
lean_dec(v_incrSaveFileName_x3f_2336_);
lean_dec(v_oleanFileName_x3f_2329_);
lean_dec(v_mainModuleName_2327_);
v_a_2661_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2642_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2642_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_runFrontend___boxed(lean_object* v_input_2670_, lean_object* v_opts_2671_, lean_object* v_fileName_2672_, lean_object* v_mainModuleName_2673_, lean_object* v_trustLevel_2674_, lean_object* v_oleanFileName_x3f_2675_, lean_object* v_ileanFileName_x3f_2676_, lean_object* v_jsonOutput_2677_, lean_object* v_errorOnKinds_2678_, lean_object* v_plugins_2679_, lean_object* v_printStats_2680_, lean_object* v_setup_x3f_2681_, lean_object* v_incrSaveFileName_x3f_2682_, lean_object* v_incrLoadFileName_x3f_2683_, lean_object* v_incrHeaderSaveFileName_x3f_2684_, lean_object* v_a_2685_){
_start:
{
uint32_t v_trustLevel_boxed_2686_; uint8_t v_jsonOutput_boxed_2687_; uint8_t v_printStats_boxed_2688_; lean_object* v_res_2689_; 
v_trustLevel_boxed_2686_ = lean_unbox_uint32(v_trustLevel_2674_);
lean_dec(v_trustLevel_2674_);
v_jsonOutput_boxed_2687_ = lean_unbox(v_jsonOutput_2677_);
v_printStats_boxed_2688_ = lean_unbox(v_printStats_2680_);
v_res_2689_ = l_Lean_Elab_runFrontend(v_input_2670_, v_opts_2671_, v_fileName_2672_, v_mainModuleName_2673_, v_trustLevel_boxed_2686_, v_oleanFileName_x3f_2675_, v_ileanFileName_x3f_2676_, v_jsonOutput_boxed_2687_, v_errorOnKinds_2678_, v_plugins_2679_, v_printStats_boxed_2688_, v_setup_x3f_2681_, v_incrSaveFileName_x3f_2682_, v_incrLoadFileName_x3f_2683_, v_incrHeaderSaveFileName_x3f_2684_);
lean_dec_ref(v_errorOnKinds_2678_);
lean_dec(v_ileanFileName_x3f_2676_);
return v_res_2689_;
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
